#
# TIGS - TI Game Setup
#
import csv
import sys
import itertools
import random
import argparse
import json

#
# Example Usages:
#
#   * Show statistics on a board:
#         python tigs.py --board 18,31,61,65,25,43,66,38,69,62,28,72,68,75,35,33,22,64,78,29,42,40,71,0,44,26,77,0,37,63,39,36,0,20,79,34,0
#
#   * Generate an unoptimized random 6-player board:
#         python tilepick.py --players 6
#
#   * Generate an optimized 6-player board:
#         python tilepick.py --players 6 --optimize
#
#   * Additional options for optimization:
#         --shuffle 3		Shuffle 3 tiles at a time each optimization step
#         --rounds 100		Do 100 rounds of optimization
#         --lock 65,66          Lock tiles 65 and 66 in their current positions
#         --require 40,42       Require tiles 40 and 42 to be part of map
#         --exclude 44,61       Exclude tiles 44 and 61 from the map
#
# Definitions:
#   home index - Index number of the home system (between 0 and n-1 for n players)
#
#   tile index - the index number of the tile as printed on the game tile.
#
#   keegan index - an index into the list of tiles as used by Keegan's tile generator.  Keegan index 0 is Mecatol, and the
#	   indices increase in concentric rings around the center starting at the top for each ring and continuing clockwise.
#
#   coord - The "cubic" coordinates of each hex tile.  We assume "flat-top" orientation of hexes.  Each hex is indexed by
#           the triple (q,r,s).  For all valid tiles, we assume q+r+s=0.  The coordinates of the center (Mecatol) is (0,0,0), and
#           we use the following rules for adjacent tiles:
#
#                     up		(0,-1,+1)
#                     down		(0,+1,-1)
#
#                     up/right 		(+1,-1,0)
#                     down/left 	(-1,+1,0)
#
#                     up/left		(-1,0,+1)
#                     down/right	(+1,0,-1)
#

#
# Factions for faction pick
#
FACTIONS=["The Arborec",
"The Barony of Letnev",
"The Clan of Saar",
"The Embers of Muaat",
"The Emirates of Hacan",
"The Federation of Sol",
"The Ghosts of Creuss",
"The L1Z1X Mindnet",
"The Mentak Coalition",
"The Naalu Collective",
"The Nekro Virus",
"Sardakk N’orr",
"The Universities of Jol-Nar",
"The Winnu",
"The Xxcha Kingdom",
"The Yin Brotherhood",
"The Yssaril Tribes",
"The Argent Flight",
"The Empyrean",
"The Mahact Gene-Sorcerers",
"The Naaz-Rokha Alliance",
"The Nomad",
"The Titans of Ul",
"The Vuil'Raith Cabal",
"The Council Keleres"]

#
# Maximum number of rings in a board
#
MAX_RINGS = 4

#
# Number of sides on a hexagon (don't change this)
#
HEX_SIDES = 6

#
# Tile index of Mecatol
#
MECATOL_INDEX = 18

#
# Base URL for Keegan's board editor
#
BASE_URL="https://keeganw.github.io/ti4/?settings=T40004892FFF&tiles="

#
# Mapping from Keegan index to hex coordinate
#
KEEGAN_TO_COORD = []

#
# Mapping from hex coordinate to a Keegan index
#
COORD_TO_KEEGAN = {}

#
# List of adjacent keegan tiles for each keegan tile
#
KEEGAN_ADJACENT = []

#
# Coordinate offsets for neighbors of a hex tile starting one hex above and proceeding clockwise.
#
NEIGHBORS = [(1,0,-1), (0,1,-1), (-1,1,0), (-1,0,1), (0,-1,1), (1,-1,0)]

#
# Weights for scoring and difference calculations
#
class WEIGHTS:
    #
    # These constants are used when calculating the difference between two
    # players positions within a "class" (1-hop, 2-hop-uncontested, etc.)
    #
    DIFF_SCORE = 1.0            # Weight for raw score
    DIFF_RES = 0.5              # Weight for total resource
    DIFF_INF = 0.5              # Weight for total infulence
    DIFF_WORM = 5.0             # Weight for wormholes
    DIFF_ANOM = 5.0             # Weight for anomalies
    DIFF_SKIP = 5.0             # Weight for tech skips

    #
    # Class weights for calculating player positions
    #
    DIFF_HOP1 = 1.0             # 1-hop
    DIFF_HOP2C = 0.125          # 2-hop-contested
    DIFF_HOP2U = 0.25           # 2-hop-uncontested


    #
    # Weights for caluclating player scores
    #
    SCORE_EFF_RESOURCE = 0.75
    SCORE_RESOURCE = 0.25
    SCORE_EFF_INFLUENCE = 0.75
    SCORE_INFLUENCE = 0.25
    SCORE_SKIPS = 0.5
    SCORE_ADJ_WORM = -2
    SCORE_HOP2_WORM = 0.25

    #
    # Min and max values for certain conditions.  If a contraint is volated, it will
    # add a -100 to the score
    #
    SCORE_MIN_HOP1_PLANET_SYS = 3
    SCORE_MAX_HOP1_PLANET_SYS = 4

    #
    # Class multipliers for player score
    #
    SCORE_HOP1 = 1.0
    SCORE_HOP2C = 0.125
    SCORE_HOP2U = 0.25


#
# List of all planets (once loaded)
#
PLANETS=[]

#
# Associative array of tiles (once loaded)
#
TILES={}

#
# Indices of home and non-home tiles
#
HOME_TILES=[]
NONHOME_TILES=[]  

#
# Return true if this is a home tile
#
def is_home(tile_index):
    if tile_index == 0:
        return True
    else:
        return TILES[tile_index]['home'] != None
    
#
# Class representing statistics for a class of tiles around a home system (e.g., 1-hop,
# 2-hop contested, 2-hop uncontested)
#
class HomeStats:
    #
    # Initialize the home statistics
    #
    def __init__(self,hop,sub_category=None):
        self.hop = hop
        self.sub_category = sub_category
        self.reset()

    #
    # Reset statistics to zeros
    #
    def reset(self):
        self.resource = 0               # Total resource
        self.influence = 0              # Total influence
        self.eff_resource = 0           # Effective resource
        self.eff_influence = 0          # Effective influence
        self.eff_both = 0               # Total of r=i planets
        self.skips = []                 # List of skips
        self.worms = 0                  # Number of wormholes
        self.anomalies = 0              # Number of anomalies
        self.planet_systems = 0         # Number of tiles with planets

    #
    # Add in statistics from another statistics object (+=)
    #
    def __iadd__(self,rhs):
        self.resource += rhs.resource
        self.influence += rhs.influence
        self.eff_resource += rhs.eff_resource
        self.eff_influence += rhs.eff_influence
        self.eff_both += rhs.eff_both
        self.skips += rhs.skips
        self.worms += rhs.worms
        self.anomalies += rhs.anomalies
        self.planet_systems += rhs.planet_systems
        return self

    #
    # Create human readable output for this statistic class
    #
    def print(self):
        print("  Hop-{}{}: r={}  i={}  er={}  ei={}  eb={}  ps={}  skips={}  worms={}   anom={}".format(
            self.hop,(" ("+self.sub_category+")" if self.sub_category else ""),
            self.resource,self.influence,self.eff_resource,self.eff_influence,self.eff_both,
            self.planet_systems, self.skips,self.worms,self.anomalies))

    #
    # Update the statistics from a list of tile_indices.  "tile_indices" is a list of
    # keegan indices of board locations, and "board" is a list of tile numbers specifying
    # the board that is being used.
    #
    def update(self,tile_indices,board):
        self.reset()
        for i in range(len(tile_indices)):
            tile_index = board[tile_indices[i]]
            if not is_home(tile_index):
                self.add_tile(TILES[tile_index])

    #
    # Accumulate statistics for a tile to this class
    #
    def add_tile(self,tile):
        for planet in tile['planets']:
            resource = int(planet['resource'])
            influence = int(planet['influence'])
            self.resource += resource
            self.influence += influence

            if resource > influence:
                self.eff_resource += resource
            elif resource < influence:
                self.eff_influence += influence
            else:
                self.eff_both += resource

        self.planet_systems += (tile['resource']+tile['influence']) > 0
        self.worms += (tile['worm'] != None)
        self.anomalies += (tile['anomaly'] != None)

        if tile['skip']:
            self.skips += [tile['skip']]

    #
    # Return a score for the this statistic class 
    #
    def score(self):
        w = [WEIGHTS.SCORE_EFF_RESOURCE,WEIGHTS.SCORE_RESOURCE,
             WEIGHTS.SCORE_EFF_INFLUENCE,WEIGHTS.SCORE_INFLUENCE,
             WEIGHTS.SCORE_SKIPS, (WEIGHTS.SCORE_ADJ_WORM if self.hop == 1 else WEIGHTS.SCORE_HOP2_WORM)]
 
        v = [self.eff_resource+self.eff_both,self.resource,self.eff_influence,self.resource,len(self.skips),self.worms]

        #
        # Base score is dot product of weight vector and value vector.  Currently the effective "both"
        # class is folded into resource for now.
        #
        _score = sum(elem[0] * elem[1] for elem in zip(w,v))

        #
        # Impose large penalties for being outside min/max number of systems /w planets
        # next to home system.
        #
        if self.hop == 1:
            if self.planet_systems > WEIGHTS.SCORE_MAX_HOP1_PLANET_SYS:
                _score += -100
            if self.planet_systems < WEIGHTS.SCORE_MIN_HOP1_PLANET_SYS:
                _score += -100
 

        return _score

    #
    # Return a score representing the difference between the statistics class and another class. 
    #
    def difference(self,other):
        diff = 0
        diff += WEIGHTS.DIFF_SCORE*abs(self.score() - other.score())
        diff += WEIGHTS.DIFF_RES*abs(self.resource-other.resource)
        diff += WEIGHTS.DIFF_INF*abs(self.influence-other.influence)
        diff += WEIGHTS.DIFF_WORM*abs(self.worms-other.worms)
        diff += WEIGHTS.DIFF_ANOM*abs(self.anomalies-other.anomalies)
        diff += WEIGHTS.DIFF_SKIP*abs(len(self.skips)-len(other.skips))

        return diff

#############################################################################
#
# Class representing a home tile
#
class Home:
    #
    # Create a home system object
    #
    def __init__(self,index,keegan,num_tiles):
        self.index = index
        self.keegan = keegan
        self.coord = KEEGAN_TO_COORD[keegan]
        self.dist_to = [cube_distance(self.coord,KEEGAN_TO_COORD[c]) for c in range(num_tiles)]

        #
        # Keegan indicies of tiles that are 'h' hops away for 0,1 and 2 hops
        #
        self.hop = [[i for i in range(len(self.dist_to)) if self.dist_to[i]==h] for h in range(3)]

    #
    # Print representation for this object
    #
    def __repr__(self):
        return "Home(index={},keegan={},coord={})".format(self.index,self.keegan,self.coord)


    #
    # Calculate the keegan indicies of the 2-hop tiles dividing into contested and uncontested
    #
    def initialize_hop2_tile_lists(self,all_homes):
        other_hop1 = set()
        other_hop2 = set()
        for i in range(len(all_homes)):
            if all_homes[i].index != self.index:
                other_hop1 = other_hop1 | set(all_homes[i].hop[1])
                other_hop2 = other_hop2 | set(all_homes[i].hop[2])

        #
        # Unconstested 2-hop tiles are those that are in our 2-hop list, but not in another home systems 1-hop or 2-hop lists
        #
        self.hop2u = [self.hop[2][i] for i in range(len(self.hop[2])) if (self.hop[2][i] not in other_hop2) and (self.hop[2][i] not in other_hop1)]

        #
        # Constested 2-hop tiles are those that are in our 2-hop list, in another players 2-hop list, but not in another home systems 1-hop list
        #
        self.hop2c = [self.hop[2][i] for i in range(len(self.hop[2])) if (self.hop[2][i] in other_hop2) and (self.hop[2][i] not in other_hop1)]

        #
        # Initialize all statistics to zero
        #
        self.stats1 = HomeStats(1)
        self.stats2u = HomeStats(2,"U")
        self.stats2c = HomeStats(2,"C")
        self.stats2t = HomeStats(2,"T")

    #
    # Reset all statistics values before recomputing
    #
    def update_stats(self,tiles):
        self.stats1.update(self.hop[1],tiles)
        self.stats2u.update(self.hop2u,tiles)
        self.stats2c.update(self.hop2c,tiles)

        self.stats2t.reset()
        self.stats2t += self.stats2u
        self.stats2t += self.stats2c

    #
    # Print a home system
    #
    def print(self):
        print("Player P{} @ #{} {}".format(self.index+1,self.keegan,self.coord))
        self.stats1.print()
        print()
        self.stats2u.print()
        self.stats2c.print()
        self.stats2t.print()

        #
        # Total effective counts
        #
        ter = self.stats1.eff_resource+self.stats2u.eff_resource + 0.5*self.stats2c.eff_resource
        tei = self.stats1.eff_influence+self.stats2u.eff_influence + 0.5*self.stats2c.eff_influence
        teb = self.stats1.eff_both+self.stats2u.eff_both + 0.5*self.stats2c.eff_both
        print()
        print("  Total Score: {}  (ter: {}, tei: {},  teb:{}  tex:{})".format(self.score(),ter,tei,teb,ter+tei+teb))

    #
    # Calculate a "goodness" score of a planet
    #
    def score(self):
        return WEIGHTS.SCORE_HOP1*self.stats1.score() + WEIGHTS.SCORE_HOP2U*self.stats2u.score() + WEIGHTS.SCORE_HOP2C*self.stats2c.score()
        


    #
    # Calculate a "difference" score between two home planets
    #
    def difference(self,other_home):
        return WEIGHTS.DIFF_HOP1*self.stats1.difference(other_home.stats1) + WEIGHTS.DIFF_HOP2C*self.stats2c.difference(other_home.stats2c) + WEIGHTS.DIFF_HOP2U*self.stats2u.difference(other_home.stats2c)

#############################################################################
#
#
#
class Board:
    #
    # Create a new board with the specified tile list in Keegan order.
    #
    def __init__(self,board=None,num_homes=6):
        self.tiles = []
        self.unused = []
        self.homes = []
        self.num_homes = 0

        #
        # Reset all tiles
        #
        if board:
            self.tiles = board.copy()
        else:
            self.tiles = self.generate_random_board(num_homes)

        #
        # Maximum keegan index we have
        #
        self.num_tiles = len(self.tiles)

        #
        # Initialize the home system stats
        #
        home_keegan = [i for i in range(len(self.tiles)) if is_home(self.tiles[i])]
        self.num_homes = len(home_keegan)
        self.homes =  [Home(i,home_keegan[i],self.num_tiles) for i in range(self.num_homes)]

        #
        # Create the contested/unconstested keegan index lists for each home
        #
        for i in range(self.num_homes):
            self.homes[i].initialize_hop2_tile_lists(self.homes)


        #
        # Build list of unused tiles
        #
        self.update_unused()

        #
        # Update board statistics
        #
        self.update_stats()

    #############################################################################
    #
    # Generate a random board for n players
    #
    def generate_random_board(self,n):
        print("generate_random_board:",n)

        #
        # Keegan numbers of home tile positions
        #
        if n == 4:
            home_keegan = [23,27,32,36]
        elif n == 6:
            home_keegan = [19,22,25,28,31,34]
        elif n == 8:
            home_keegan = [37,40,43,46,49,52,55,58]
        else:
            raise Exception("Unsupported player count")

        #
        # Number of tiles on board based on player count
        #
        num_tiles = 37 if n <= 6 else 61

        #
        # Get all (non-home) tiles (except first one which is Mecatol)
        #
        all_tiles = [i for i in NONHOME_TILES if i != MECATOL_INDEX]

        #
        # Always include Mecatol Rex and the required tiles
        #
        tile_list = [MECATOL_INDEX] + list(FLAGS.require)

        #
        # Remove the required tiles from "all_tiles" since they have already been assigned
        #
        for r in FLAGS.require:
            del all_tiles[all_tiles.index(r)]

        #
        # Randomize other tiles
        #
        tile_list += random.sample(all_tiles,num_tiles-len(tile_list)-n)

        #
        # Insert the home systems
        #
        for k in home_keegan:
            tile_list.insert(k,0)

        return tile_list

    #
    # Generate a url for the current board state
    #
    def get_url(self):
        tiles = [t for t in self.tiles]

        while True:
            t = tiles.pop()
            if t >= 0:
                tiles += [t]
                break
            
        return BASE_URL+",".join(map(str,tiles))
            

    #
    # Update list of unused tiles
    #
    def update_unused(self):
        self.unused = [tile for tile in NONHOME_TILES if tile not in self.tiles and tile not in FLAGS.exclude]

    #
    # Update statistics for all home systems
    #
    def update_stats(self):
        for h in range(len(self.homes)):
            self.homes[h].update_stats(self.tiles)

    #
    # Print statistic summary of board
    #
    def print(self):
        for hi in range(len(self.homes)):
            self.homes[hi].print()
            print()

        print("Total Imbalance: ",self.get_imbalance())

    #
    # Get the imbalance board for the current board state.  The global imbalance score
    # is the laregest difference score between any two home systems.
    #
    def get_imbalance(self):
        max_diff = 0
        for pair in itertools.combinations(range(self.num_homes),2):
            diff = self.homes[pair[0]].difference(self.homes[pair[1]])
            if diff > max_diff:
                max_diff = diff
        return max_diff

    #
    # Optimize the current board state by trying to improve it over a specified number of steps
    #
    def optimize(self, steps):
        for i in range(steps):
            imbalance = board.get_imbalance()
            print("{}:imbalance={}".format(i,imbalance))
            if imbalance == 0:
                return 0
            board.improve()
        return board.get_imbalance()

    #
    # Check a set of tiles (by keegan index) for validity
    #
    def is_valid(self,keegan):
        tile = TILES[self.tiles[keegan]]

        #
        # No adjacent anomalies
        #
        if tile['anomaly']:
            if any(self.tiles[k] > 0 and TILES[self.tiles[k]]['anomaly'] != None for k in KEEGAN_ADJACENT[keegan] if k < self.num_tiles):
                return False

        #
        # No adjacent wormholes of same type
        #
        if tile['worm']:
            if any(self.tiles[k] > 0 and tile['worm'] == TILES[self.tiles[k]]['worm'] for k in KEEGAN_ADJACENT[keegan] if k < self.num_tiles):
                return False

        #
        # No legandary planets adjacent to a player
        #
        if tile['skip'] == 'legend':
            if any(self.tiles[k] == 0 for k in KEEGAN_ADJACENT[keegan] if k < self.num_tiles):
                return False

        #
        # No wormholes adjacent to a player
        #
        if tile['worm']:
            if any(self.tiles[k] == 0 for k in KEEGAN_ADJACENT[keegan] if k < self.num_tiles):
                return False
           
        return True

    #
    # Try to improve a board
    #
    def improve(self):
        #
        # choose num_shuffle tiles to use for shuffling
        #
        shuffle_keegan = []
        for i in range(FLAGS.shuffle):
            while True:
                keegan = random.randint(1,self.num_tiles-1)

                #
                # We already picked this position
                #
                if keegan in shuffle_keegan:
                    continue

                #
                # Don't shuffle home tiles
                #
                if is_home(self.tiles[keegan]):
                    continue

                #
                # Don't shuffle positions with locked tiles
                #
                if FLAGS.lock and self.tiles[keegan] in FLAGS.lock:
                    continue

                #
                # Everything looks good.
                #
                break

            #
            # Add to tile positions to be shuffled
            #
            shuffle_keegan += [keegan]

        #
        # List of free tiles to try in the keegan indices in the shuffle set.  This includes
        # the tiles that we just "lifted" from the shuffle_keegan set, and all the currently
        # free tiles.
        #
        free_tiles = [self.tiles[i] for i in shuffle_keegan] + self.unused

        #
        # Get current imbalance and tiles
        #
        best_imbalance = self.get_imbalance()
        best_tiles = [self.tiles[shuffle_keegan[i]] for i in range(FLAGS.shuffle)]

        #
        # Iterate through all permutations of num_shuffle tiles in the free tiles set.
        #
        for tiles in itertools.permutations(free_tiles,FLAGS.shuffle):
            for i in range(FLAGS.shuffle):
                self.tiles[shuffle_keegan[i]] = tiles[i]


            #
            # Check validity of all tiles we want to place.  Skip this permutation
            # if there is an invalid tile placement.
            #
            if not all(self.is_valid(shuffle_keegan[i]) for i in range(FLAGS.shuffle)):
                continue

            #
            # Update statistics in new board
            #
            self.update_stats()

            #
            # Calculate the current imbalance.  Update the best imbalance the best tile
            # permutation if it is the best we have seen so far.
            #
            imbalance = self.get_imbalance()
            if imbalance < best_imbalance:
                best_imbalance = imbalance
                best_tiles = [self.tiles[shuffle_keegan[i]] for i in range(FLAGS.shuffle)]

        #
        # Insert the best tiles we found back into the map
        #
        for i in range(FLAGS.shuffle):
            self.tiles[shuffle_keegan[i]] = best_tiles[i]

        #
        # Update the unused tile list
        #
        self.update_stats()
        self.update_unused()

########################################################################################
#
# Convert string with a comma separated list of integers into an actual list of integers, or an empty list if
# the string is empty or None.
#
def to_tile_list(s):
    if s:
        return list(map(int,s.split(",")))
    else:
        return []

########################################################################################
#
# Add two cube coodinates
#
def cube_add(x,y):
    return tuple(map(sum,zip(x,y)))

########################################################################################
#
# Distance between two cube coodinates
#
def cube_distance(x,y):
    return max(abs(x[0]-y[0]), abs(x[1]-y[1]), abs(x[2]-y[2]))

########################################################################################
#
# Get the ring number of a cube coodinate
#
def cube_ring_number(x):
    return max(abs(x[0]), abs(x[1]), abs(x[2]))

#############################################################################
#
# Get list of offsets for the nth ring
#
def cube_ring(n):
    if n <= 0:
        return [(0,0,0)]

    RING = []
    coord = (0,-n,n)

    for side in NEIGHBORS:
        for k in range(n):
            RING += [coord]
            coord = cube_add(coord,side)

    return RING

    
########################################################################################
#
# Initialize the mapping from a keegan index to its cubic coordinate
#
def init_hex_coords():
    global COORD_TO_KEEGAN, KEEGAN_TO_COORD, KEEGAN_ADJACENT

    #
    # Create mapping from keegan index to hex coodinate
    #
    KEEGAN_TO_COORD = [coord for ring in range(MAX_RINGS+1) for coord in cube_ring(ring)]
    
    #
    # Create the inverse mapping from hex coodinate to slot
    #
    COORD_TO_KEEGAN = { KEEGAN_TO_COORD[k]:k for k in range(len(KEEGAN_TO_COORD))}

    #
    # Create list of tiles adjacent to each tile
    #
    for k in range(len(KEEGAN_TO_COORD)):
        coord = KEEGAN_TO_COORD[k]
        adjacent = []
        for offset in NEIGHBORS:
            n_coord = cube_add(coord,offset)
            if n_coord in COORD_TO_KEEGAN:
                adjacent += [COORD_TO_KEEGAN[n_coord]]
                
        KEEGAN_ADJACENT += [adjacent]
                
#########################################################################################
#
# Load all the tiles from data file
#
def load_tiles():
    global PLANETS, TILES, HOME_TILES, NONHOME_TILES

    with open('planets.csv') as f:
        reader = csv.reader(f,delimiter=',')
        for row in reader:
            while len(row) < 8:
                row += ['']

            index = int(row[0])

            #
            # Get the planet type for special handling
            #
            planet_type = (row[4]).strip()
            is_home = planet_type == 'home'

            if is_home:
                planet = {
                    'tile': index,
                    'name': (row[1]).strip(),
                    'resource': int(row[2]),
                    'influence': int(row[3]),
                    'type': planet_type,
                    'skip':"",
                    'anomaly':"",
                    'worm':"",
                }
            else:
                planet = {
                    'tile': index,
                    'name': (row[1]).strip(),
                    'resource': int(row[2]),
                    'influence': int(row[3]),
                    'type': planet_type,
                    'skip': (row[5]).strip(),
                    'anomaly': row[6].strip(),
                    'worm': row[7].strip(),
                }

            if FLAGS.effective:
                if planet['resource'] >= planet['influence']:
                    planet['influence'] = 0
                else:
                    planet['resource'] = 0
                

            #
            # "home" in the type field indicates this is a home system
            #

            PLANETS += [planet]

            if index in TILES:
                tile = TILES[index]
            else:
                tile = {'resource':0,'influence':0,'skip':None, 'anomaly':None, 'worm':None, 'planets':[]}
                if is_home:
                    HOME_TILES += [index]
                    tile['home'] = planet['skip']
                else:
                    NONHOME_TILES += [index]
                    tile['home'] = None

                #
                # Add the tile
                #
                TILES[index] = tile

            tile['planets'] += [planet]
            tile['resource'] += planet['resource']
            tile['influence'] += planet['influence']


            #
            # Ignore these fields for home systems
            #
            if not is_home:
                tile['skip'] = planet['skip'] if planet['skip'] != '' else tile['skip']
                tile['anomaly'] = planet['anomaly'] if planet['anomaly'] != '' else tile['anomaly']
                tile['worm'] = planet['worm'] if planet['worm'] != '' else tile['worm']

########################################################################################
#
# Tile analysis main function
#
def main_board():
    global board

    #
    # Initialize the hex coordinate system
    #
    init_hex_coords()

    #
    # Load the tile set
    #
    load_tiles()

    #
    # Create the board either with a specific tile set, or with a number of players
    #
    if FLAGS.board:
        board = Board(board=FLAGS.board)
    else:
        board = Board(num_homes=FLAGS.players)

    #
    # Do the optimization if the --optimize flag was used
    #
    if FLAGS.optimize:
        board.optimize(FLAGS.rounds)

    #
    # Show statistics
    #
    board.print()

    #
    # Print the generated URL
    #
    print()
    print(board.get_url())

#
# Select faction choices for players
#
def main_factions(names):
    num_names = len(names)

    random.shuffle(FACTIONS)
    num_per = len(FACTIONS) // num_names

    for i in range(num_names):
        print(names[i]+":")
        for j in range(num_per):
            print("   ",FACTIONS[i*num_per+j])

#
# Select positions for players
#
def main_positions(names):
    random.shuffle(names)
    for i in range(len(names)):
        print("P{}: {}".format(i+1,names[i]))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    
    parser.add_argument('--optimize',action='store_true',help="Optimize tiles")
    parser.add_argument('--factions',action='store_true',help="Select Factions")
    parser.add_argument('--positions',action='store_true',help="Select Positions")
    parser.add_argument('--effective',action='store_true',help="Use 'effective' resource/influence values")
    
    parser.add_argument('--board',type=str,default=None,help="Specify an initial board")
    parser.add_argument('--players',type=int,default=4,help="Number of players")
    parser.add_argument('--rounds',type=int,default=100,help="Number of rounds of optimization to do")
    parser.add_argument('--shuffle',type=int,default=3,help="Number of tiles to shuffle at a time")
    parser.add_argument('--require',type=str,default=None,help="tiles to require on map")
    parser.add_argument('--lock',type=str,default=None,help="lock tiles in place on map")
    parser.add_argument('--exclude',type=str,default=None,help="tiles to exclude from map")

    parser.add_argument('names',type=str,nargs='*',default=None,help="List of player names")


    FLAGS = parser.parse_args()


    FLAGS.board = to_tile_list(FLAGS.board)
    FLAGS.require = set(to_tile_list(FLAGS.require))
    FLAGS.exclude = set(to_tile_list(FLAGS.exclude))
    FLAGS.lock = set(to_tile_list(FLAGS.lock))

    if FLAGS.factions:
        main_factions(FLAGS.names)
    elif FLAGS.positions:
        main_positions(FLAGS.names)
    else:
        main_board()

