#!/usr/bin/python
# convertMavensHH.py
# Steve Grantz steve@degen.club
# 2020-05-12
# Usage:
# python convertMavensHH.py file.txt [file2.txt ...]

############################################################################################################
# WHAT THIS DOES
#
# goal of this program is to process Poker Mavens hand history text and convert to JSON format
# that matches the Standardized hand History format specified by PokerTracker and documented here:
#  https://hh-specs.handhistory.org/
#
# To do this we will take the logs and first break it up into hand by hand
#
# Then we can loop through each hand, and convert to the JSON format specified.
# Finally, we output the new JSON.
#
# KEY ASSUMPTIONS
#
# Working with Ring games only, not tournaments
#
# CHANGE LOG
# 2020-05-12 first version
# 2020-11-28 fixes for first import (always include showdown round 4)
# 2020-11-28 make external configuration file


import argparse
import configparser
import datetime
import json
import pytz
import re
import sys

# constants - DO NOT CHANGE
VERSION = "0.1"
OPTIONS_FILE = "convertMavensHH.ini"
INDEX = "index"
TEXT = "text"
FIRST = "first"
LATEST = "latest"
LAST = "last"
IN = "cash in"
OUT = "cash out"
WAITING = "sitting out"
LEFT = "left table"
NOTES = "notes"
TABLE="table"
GAME="game"
COUNT="count"
DATETIME="datetime"
HANDLE="handle"
NAME="name"
DISPLAY="display"
POSTS_BOTH_BLINDS = 'posts small & big blind'
HOLE_CARDS = "Hole Cards"
SHOW_DOWN = "Show Down"
SHOWDOWN_ROUND_ID = 4

# OHH field name and known constant values
# DO NOT CHANGE
SPEC_VERSION = "spec_version"
OHH_VERSION = "1.2.2"
OHH="ohh"
SITE_NAME = "site_name"
NETWORK_NAME = "network_name"
MAVENS="Poker Mavens"
INTERNAL_VERSION = "internal_version"
HH_VERSION = "1.0.0"
GAME_NUMBER = "game_number"
START_DATE_UTC = "start_date_utc"
TABLE_NAME = "table_name"
TABLE_HANDLE = "table_handle"
GAME_TYPE = "game_type"
BET_LIMIT = "bet_limit"
BET_TYPE = "bet_type"
BET_CAP = "bet_cap"
TABLE_SIZE = "table_size"
CURRENCY = "currency"
DEALER_SEAT = "dealer_seat"
SMALL_BLIND = "small_blind_amount"
BIG_BLIND = "big_blind_amount"
ANTE = "ante_amount"
HERO = "hero_player_id"
ID="id"
SEAT="seat"
STARTING_STACK="starting_stack"
FLAGS="flags"
OBSERVED="observed"
PLAYERS="players"
ROUNDS="rounds"
POTS="pots"
STREET="street"
CARDS="cards"
ACTIONS="actions"
ACTION="action"
ACTION_NUMBER="action_number"
PLAYER_ID="player_id"
AMOUNT="amount"
IS_ALL_IN = "is_allin"
NUMBER = "number"
RAKE = "rake"
PLAYER_WINS = "player_wins"
WIN_AMOUNT = "win_amount"
CONTRIBUTED_RAKE = "contributed_rake"

# constants for processing INI and setting configurable defaults
HERO_NAME = "HeroName"
TIMEZONE_TEXT= "TimeZone"
CURRENCY_ABBR = "CurrencyAbbr"
PREFIX = "OutputPrefix"
# end script level constants

# configurable constants
# these are constants that are meant to be configurable - they could be edited here,
# or specified in a configuration file that is external to this script and checked for at run time
DEFAULT_OPTIONS = {
    HERO_NAME: "hero",
    TIMEZONE_TEXT: "America/New_York",
    CURRENCY_ABBR: "PPC",
    PREFIX: "HHC"
}

# end configurable constants

##################################################################################################################
#
# DATA STRUCTURES
#
hands = {}    # the hands dictionary
              # display
              # KEY - string - hand number
              # DATETIME - datetime - timestamp for the hand
              # TABLE - string - table where the hand happened
              # TEXT  - string - full text of hand, with newlines

tables = {}   # the tables dictionary
              # structure
              # KEY - string - table name as found in log
              # COUNT - integer - number of hands processed for table
              # LATEST - datetime - the latest time stamp for a hand processed for this table
              # LAST - string - hand number for the latest hand processed for this table
              #        LAST and LATEST are used to mark the "end" activity of players standing up
              #        they represent the last seen hand at the table from the processed logs
              # HANDLE - absolute value of the hash value of the name of the table, as a string
              # OHH - list of hand histories, each in JSON following the OHH format

# lookup tables
structures = {
    "Limit":"FL",
    "PL":"PL",
    "NL":"NL"
}

games = {
    "Hold'em":"Holdem",
    "Omaha Hi-Lo": "OmahaHiLo",
    "Omaha": "Omaha",
    "Omaha-5": "Omaha",
    "Omaha-5 Hi-Lo": "OmahaHiLo",
    "Stud Hi-Lo": "StudHiLo",
    "Stud" : "Stud",
    "Razz" : "Stud"
}

requireShowdown = [
    "Holdem",
    "Omaha",
    "OmahaHiLo"
]

postTypes = {
    "posts ante":"Post Ante",
    "posts big blind":"Post BB",
    "posts small blind":"Post SB",
    "posts straddle": "Straddle",
}

firstRounds = {
    "Holdem": "Preflop",
    "Omaha": "Preflop",
    "OmahaHiLo": "Preflop",
    "Stud": "Third Street",
    "StudHiLo": "Third Street"
}

makeNewRound = {
    "Flop":"Flop",
    "Turn": "Turn",
    "River": "River",
    "4th Street": "Fourth Street",
    "5th Street": "Fifth Street",
    "6th Street": "Sixth Street",
    "Show Down" : "Showdown"
}

betVerbToAction = {
    "bets":"Bet",
    "brings in for":"Bring In",
    "calls":"Call",
    "raises to":"Raise"
}

# end of data structures
#
#######################################################################################################################

##################################################################################################################
#
# FUNCTIONS
#

# end of functions
#
#######################################################################################################################

lineCount = 0
sessionDate = datetime.datetime.now().strftime("%m/%d/%Y")

# look for configuration file and use those settings
# then load player roster if specified and found
# finally if there is an EmailExportFile specified, open that,
# parse each line, and either update or create a resolvedScreenName dictionary entry using
# the combination of ScreenName and email on each line of that file
# the export file format is that which Mavens produces from the
# Accounts tab "Export > Emails With Names" option
config = configparser.ConfigParser(defaults=DEFAULT_OPTIONS)
try:
    with open(OPTIONS_FILE,encoding="utf-8") as optionsFile:
        config.read_file(optionsFile)

except IOError:
    optionInformation = "Could not read " + OPTIONS_FILE + ". Using default values from script."



# get and parse command line arguments
# then process some key ones straight away
# namely, if roster option is used, dump the player roster and go
# if email option is activated, check for presence of password command line argument
# if not there prompt for it
parser = argparse.ArgumentParser(description=
                                 ('Convert Poker Mavens hand history to JSON.' +
                                  ' v ' + VERSION))
parser.add_argument('-c','--currency', action="store",dest="currency",default=config.get('DEFAULT',CURRENCY_ABBR),
                    help=("Three letter currency code to specify in converted hand histories. " +
                            "Default: " + config.get('DEFAULT',CURRENCY_ABBR))
                    )
parser.add_argument('-i','--indent', action="store_true",dest="indent",default=False,
                    help="Indent JSON output. Violates specified .ohh file format, but useful for debugging.")
parser.add_argument('-p','--player', action="store",dest="player",default=config.get('DEFAULT',HERO_NAME),
                    help="The screen name for our hero player. Default: " + config.get('DEFAULT',HERO_NAME))
parser.add_argument('-t','--timezone', action="store",dest="timezone",default=config.get('DEFAULT',TIMEZONE_TEXT),
                    help=("Timezone specification for hand history times. In form \"Asia/Macau\". " +
                            " For list see https://en.wikipedia.org/wiki/List_of_tz_database_time_zones. " +
                            "Default: " + config.get('DEFAULT',TIMEZONE_TEXT) )
                   )
parser.add_argument('file', type=argparse.FileType('r'), nargs='*',help="plain text files of Poker Mavens hand histories to process.")
args = parser.parse_args()

lastHandTime = datetime.datetime.now()
heroPlayer = args.player

currency = args.currency
if (len(currency) != 3):
    print("Currency code must have three characters. Defaulting back to " + DEFAULT_CURRENCY)
    currency = DEFAULT_CURRENCY

timezone = pytz.timezone(args.timezone)

numArg = len(args.file)
if (numArg == 0):
    print("Must provide a name of a log file to process.")
else:
    # process each file listed on the command line
    # first loop through is just to parse and get each hand separated, and get basic hand
    # info into the hands dictionary
    # basic hand info is hand number, local hand number, hand time, and table
    # everything else goes into TEXT
    for fh in args.file:
        f = open(fh.name, mode='r', encoding='utf-8')
        line = f.readline()
        while (len(line) != 0):
            matches = re.search("Hand #(\d*-\d*) - (.*)$",line)
            if (matches != None):
                handNumber = matches.group(1)
                handTime = datetime.datetime.strptime(matches.group(2),"%Y-%m-%d %H:%M:%S")
                hands[handNumber] = {
                                   DATETIME: handTime,
                                   TEXT: ''}
                line = f.readline()
                while (not (line.strip() == '')):
                    table = re.search("Table: (.*)$",line)
                    if (table != None):
                        tableName = table.group(1)
                        if (not tableName in tables):
                            tables[tableName] = {COUNT: 0, LATEST: "", OHH:[] }
                            tables[tableName][HANDLE] = str(abs(hash(tableName)))
                        hands[handNumber][TABLE] = tableName
                    hands[handNumber][TEXT] = hands[handNumber][TEXT] + line
                    line = f.readline()
            else:
                line = f.readline()
        f.close()

    handNumber = ""
    handTime = datetime.datetime.now()

    # now that we have all hands from all the files,
    # use the timestamps of the imported hands to process them in chronological order
    # this is the place for processing the text of each hand and look for player actions
    for handNumber in sorted(hands.keys(), key=lambda hand: hands[hand][DATETIME] ):

        # Get important hand and table header info and put hand time in the YYYY-mm-ddThh:mm:ssZ ISO
        # format that is expected by the OHH spec
        # being sure to reference back to the timezone as specified in command line
        # or configuration files
        handTime = timezone.localize(hands[handNumber][DATETIME])
        handTimeUtc = handTime.astimezone(pytz.utc).strftime("%Y-%m-%dT%TZ")
        # print(handNumber) #DEBUG
        table = hands[handNumber][TABLE]
        tables[table][COUNT] += 1
        tables[table][LATEST] = handTime
        tables[table][LAST] = handNumber
        lastHandTime = handTime
        # print(handTime) # DEBUG

        # initialize the OHH JSON populating as many fields as possible and initializing key arrays
        # like FLAGS, PLAYERS, ROUNDS, POTS
        ohh = { SPEC_VERSION: OHH_VERSION,
                SITE_NAME: '',
                NETWORK_NAME: '',
                INTERNAL_VERSION: HH_VERSION,
                GAME_NUMBER: handNumber,
                START_DATE_UTC : handTimeUtc,
                TABLE_NAME : table,
                TABLE_HANDLE : tables[table][HANDLE],
                GAME_TYPE : "",
                BET_LIMIT : {},
                TABLE_SIZE : 10,
                CURRENCY: currency,
                DEALER_SEAT : 1,
                SMALL_BLIND : 0,
                BIG_BLIND : 0,
                ANTE : 0,
                FLAGS:[],
                PLAYERS:[],
                ROUNDS:[],
                POTS:[]
                }
        players = []
        playerIds = {}


        # Set some Boolean flags to indicate what we already know about the Hand
        # For instance processedSeats is set to False
        # but once we know we have seenSeats we can assume we are either in or past that
        # part of chat history and do not need to do text searches for Site, Game
        # Also a placeholder for current Round
        # processedSeats is a marker for the parsing logic to indicate we hace already
        # encountered the players in the hands and accounted for them
        # similar markers are used for cardsDealt and currentRound
        processedSeats = False
        cardsDealt = False
        currentRound = None
        heroPlaying = False
        winners = []
        roundNumber = 0
        actionNumber = 0
        round = { CARDS:[], ACTIONS:[]}
        pots = {}


        for line in hands[handNumber][TEXT].splitlines():
            if (not cardsDealt):
                if (not processedSeats):
                    # the text match to look for the site name
                    site = re.search("Site: (.+)$",line)
                    if (site != None):
                        ohh[SITE_NAME] = site.group(1)
                        ohh[NETWORK_NAME] = site.group(1)
                        continue

                    # the text match to look for the game type
                    game = re.search("Game: (\w+) ([^\(]+) \([^\)]+\)(.*)$",line)
                    if (game != None):
                        structure = game.group(1)
                        variant = game.group(2)
                        terms = game.group(3)

                        if (variant in games):
                            ohh[GAME_TYPE] = games[variant]
                        else:
                            print("Game variant not found: " + variant + " for hand: " + handNumber)

                        if (structure in structures):
                            ohh[BET_LIMIT][BET_TYPE] = structures[structure]
                        else:
                            print("Structure not found: " + structure + " for hand: " + handNumber)

                        blinds = re.search("Blinds ([\d.]+)/([\d.]+)", terms)
                        if (blinds != None):
                            ohh[SMALL_BLIND] = float(blinds.group(1))
                            ohh[BIG_BLIND] = float(blinds.group(2))

                        ante = re.search("Ante ([\d.]+)", terms)
                        if (ante != None):
                            ohh[ANTE] = float(ante.group(1))

                        continue

                # the text match to look for a seated player and see their chip amount
                # specifically for the hero player, make sure that the player is not
                # waiting or sitting out, and then mark the hand appropriately
                # for the ID for Hero or the Flag for Observed
                seat = re.search("Seat (\d+): (\w+) \(([\d.]+)\)",line)
                if (seat != None):
                    seatNumber = int(seat.group(1))
                    player = seat.group(2)
                    stack = float(seat.group(3))
                    players.append({ID:seatNumber,
                                    SEAT:seatNumber,
                                    NAME:player,
                                    DISPLAY:player,
                                    STARTING_STACK: stack})
                    playerIds[player] = seatNumber
                    if (player == heroPlayer):
                        ohh[HERO] = seatNumber
                        sitOrWait = re.search("(sitting|waiting)", line)
                        if (sitOrWait is None):
                            heroPlaying = True
                    processedSeats = True
                    continue

                # the text to match for an add on
                buttonSpecified = re.search("(.+) has the dealer button",line)
                if (buttonSpecified != None):
                    buttonPlayer = buttonSpecified.group(1)
                    ohh[DEALER_SEAT] = playerIds[buttonPlayer]

            # the text to match for a post
            # this also indicates that the dealing is happening and we should
            # move to the phase of assembling rounds of actions
            # currently do not use the OHH action of "Post Extra Blind" or "Post Dead"
            #TODO test scenarios with dead blind or additional blind
            #TODO Check if an allin post results in comment on the post line itself
            post = re.search("^(\w+) (posts .*) ([\d.]+)$",line)
            if (post != None):
                player = post.group(1)
                type = post.group(2)
                amount = float(post.group(3))
                cardsDealt = True
                if (currentRound is None):
                    actionNumber = 0
                    round[ID] = (roundNumber)
                    currentRound = firstRounds[ohh[GAME_TYPE]]
                    round[STREET] = currentRound
                action = {}
                if (type == POSTS_BOTH_BLINDS):
                    action[ACTION_NUMBER] = actionNumber
                    action[PLAYER_ID] = playerIds[player]
                    action[AMOUNT] = ohh[SMALL_BLIND]
                    action[ACTION] = "Post SB"
                    round[ACTIONS].append(action)
                    actionNumber += 1
                    action = {}
                    action[ACTION_NUMBER] = actionNumber
                    action[PLAYER_ID] = playerIds[player]
                    action[AMOUNT] = ohh[BIG_BLIND]
                    action[ACTION] = "Post BB"
                    round[ACTIONS].append(action)
                else:
                    action[ACTION_NUMBER] = actionNumber
                    action[PLAYER_ID] = playerIds[player]
                    action[AMOUNT] = amount
                    action[ACTION] = postTypes[type]
                    round[ACTIONS].append(action)
                actionNumber += 1

            # look for round markers
            # note that cards dealt are melded together with opening round and do not necessarily mark a new round
            roundMarker = re.search("\*\* ([^\*]+) \*\*",line)
            if (roundMarker != None):
                label = roundMarker.group(1)
                notes = re.search("\*\* \[([^\[]*)\]", line)
                # should not happen that we get to this point without a post
                # but let's anticipate that it could happen and check for that when
                # processing hole cards
                if (roundMarker == HOLE_CARDS):
                    if (currentRound is None):
                        actionNumber = 0
                        round[ID] = (roundNumber)
                        currentRound = firstRounds[ohh[GAME_TYPE]]
                        round[STREET] = currentRound
                        action = {}
                    continue
                elif (label in makeNewRound):
                    # make new round
                    # we need to add current round object to the OHH JSON
                    # and make a clean one
                    # increment round number and reset action number
                    ohh[ROUNDS].append(round)
                    round = {}
                    roundNumber += 1
                    actionNumber = 0
                    thisRound = makeNewRound[label]
                    currentRound = thisRound
                    round[ID] = (roundNumber)
                    round[STREET] = currentRound
                    round[CARDS] = []
                    round[ACTIONS] = []
                    if (notes is not None):
                        for card in notes.group(1).split():
                            round[CARDS].append(card)
                elif (SHOW_DOWN in label):
                    ohh[ROUNDS].append(round)
                    round = {}
                    roundNumber += 1
                    actionNumber = 0
                    currentRound = label
                    round[ID] = (roundNumber)
                    round[STREET] = makeNewRound[SHOW_DOWN]
                    round[CARDS] = []
                    round[ACTIONS] = []
                else:
                    continue

            # the text to match for an add on
            addOn = re.search("(\w+) adds ([\d.]+) chip",line)
            if (addOn != None):
                player = addOn.group(1)
                additional = float(addOn.group(2))
                if (currentRound is not None and player in playerIds):
                    action={}
                    action[ACTION_NUMBER] = actionNumber
                    action[PLAYER_ID] = (playerIds[player])
                    action[AMOUNT] = additional
                    action[ACTION] = "Added Chips"
                    round[ACTIONS].append(action)
                    actionNumber += 1
                continue

            # the text to match for cards dealt
            dealt = re.search("Dealt to (\w+) \[([^\]]*)\]",line)
            if (dealt != None):
                player = dealt.group(1)
                cards = dealt.group(2)
                action = {}
                action[ACTION_NUMBER] = actionNumber
                action[PLAYER_ID] = playerIds[player]
                action[ACTION] = "Dealt Cards"
                action[CARDS] = []
                for card in cards.split():
                    action[CARDS].append(card)
                round[ACTIONS].append(action)
                actionNumber += 1
                continue

            # the text to match for folds
            checks = re.search("(\w+) checks",line)
            if (checks != None):
                player = checks.group(1)
                action = {}
                action[ACTION_NUMBER] = actionNumber
                action[PLAYER_ID] = playerIds[player]
                action[ACTION] = "Check"
                round[ACTIONS].append(action)
                actionNumber += 1
                continue

            # the text to match for checks
            folds = re.search("(\w+) folds",line)
            if (folds != None):
                player = folds.group(1)
                action = {}
                action[ACTION_NUMBER] = actionNumber
                action[PLAYER_ID] = playerIds[player]
                action[ACTION] = "Fold"
                round[ACTIONS].append(action)
                actionNumber += 1
                continue

            # the text to match for betting
            # important to look for All-in indicator and mark the action
            # as such inthe hand history
            bet = re.search("(\w+) (bets|calls|raises to|brings in for) ([\d.]+)",line)
            if (bet != None):
                player = bet.group(1)
                does =  bet.group(2)
                amount = float(bet.group(3))
                action={}
                action[ACTION_NUMBER] = actionNumber
                action[PLAYER_ID] = playerIds[player]
                action[AMOUNT] = amount
                action[ACTION] = betVerbToAction[does]
                allIn = re.search("\(All-in\)",line)
                if (allIn is not None):
                    action[IS_ALL_IN] = True
                round[ACTIONS].append(action)
                actionNumber += 1
                continue

            # the text to match for showing card
            shows = re.search("(\w+) shows \[([^\]]*)\]",line)
            if (shows != None):
                player = shows.group(1)
                cards = shows.group(2)
                action = {}
                action[ACTION_NUMBER] = actionNumber
                action[PLAYER_ID] = playerIds[player]
                action[ACTION] = "Shows Cards"
                action[CARDS] = []
                for card in cards.split():
                    action[CARDS].append(card)
                round[ACTIONS].append(action)
                actionNumber += 1
                continue

            # the text to match for a refunded bet
            # during initial development, it was not clear how to handle refunded bets
            # since the OHH spec does not mention these
            # so the initial approach was to add these into the pot so that the rewarded pot
            # added up to what was bet
            # however on initial testing, became clear that this is not an issue
            # PT4 on import accounts for uncalled bets and does not include them
            # in pot calculations
            # so the pot calculation here is commented out
            #TODO remove this refunded processing entirely if truly not needed
            refunded = re.search("(\w+) refunded ([\d.]+)",line)
            if (refunded != None):
                player = refunded.group(1)
                amount = float(refunded.group(2))
                playerId = playerIds[player]
                potNumber = 0
                #if (not potNumber in pots):
                #    pots[potNumber] = {NUMBER: potNumber, AMOUNT: 0, RAKE: 0, PLAYER_WINS: {}}
                #    if (not playerId in pots[potNumber][PLAYER_WINS]):
                #        pots[potNumber][PLAYER_WINS][playerId] = {PLAYER_ID: playerId, WIN_AMOUNT: 0, CONTRIBUTED_RAKE:0}
                #pots[potNumber][AMOUNT] += amount
                #pots[potNumber][PLAYER_WINS][playerId][WIN_AMOUNT] += amount
                continue

            # the text to match for cards shows
            # the text to check for a win
            # the winners array is used in later logic to check
            # for the existence of showdown round 4 in each OHH object
            winner = re.search("(\w+) (wins|splits).*Pot (\d+)? *\(([\d.]+)\)",line)
            if (winner != None):
                player = winner.group(1)
                playerId = playerIds[player]
                winners.append(playerId)
                potNumber = int(winner.group(3)) if (winner.group(3) is not None) else 0
                win = float(winner.group(4))
                if (not potNumber in pots):
                    pots[potNumber] = {NUMBER: potNumber, AMOUNT: 0, RAKE: 0, PLAYER_WINS: {}}
                if (not playerId in pots[potNumber][PLAYER_WINS]):
                    pots[potNumber][PLAYER_WINS][playerId] = {PLAYER_ID: playerId, WIN_AMOUNT: 0, CONTRIBUTED_RAKE:0}
                pots[potNumber][AMOUNT] += win
                pots[potNumber][PLAYER_WINS][playerId][WIN_AMOUNT] += win

        # Need to step through the pots dictionary of dictionaries
        # and rewrite each pot as a potObject that is then added to the POTS list in the OHH JSON
        # so that the OHH JSON is as expected
        # then we can add that to the OHH JSON
        for potNumber in pots.keys():
            amt = pots[potNumber][AMOUNT]
            rake = pots[potNumber][RAKE]
            potObj = {NUMBER: potNumber,
                      AMOUNT: amt,
                      RAKE: rake,
                      PLAYER_WINS: []
                      }
            for playerId in pots[potNumber][PLAYER_WINS]:
                winAmt = pots[potNumber][PLAYER_WINS][playerId][WIN_AMOUNT]
                rakeContribution = pots[potNumber][PLAYER_WINS][playerId][CONTRIBUTED_RAKE]
                playerWinObj = {PLAYER_ID:playerId,
                                WIN_AMOUNT: winAmt,
                                CONTRIBUTED_RAKE: rakeContribution
                                }
                potObj[PLAYER_WINS].append(playerWinObj)

            ohh[POTS].append(potObj)


        # final cleanup and assignments before pushing the JSON onto the list for the table
        # including requirement from the OHH spec that there MUST be a round 4 (showdown)
        # only going to check this if the game is Hold 'Em or Omaha (does not make sense for Stud)
        # and prepared to remove this if the spec is adjusted for what appears to be a mistake
        if (not heroPlaying):
            ohh[FLAGS].append(OBSERVED)
        ohh[PLAYERS] = players
        ohh[ROUNDS].append(round)
        # now check if there should be a round 4 according to spec but it is absent
        # and if not there then add it
        # error out if somehow more than one winner (there should have been a showdown to produce
        # more than one winner)
        if (ohh[GAME_TYPE] in requireShowdown):
            hasShowdownRound = False
            for round in ohh[ROUNDS]:
                if (round[ID] == SHOWDOWN_ROUND_ID):
                    hasShowdownRound = True
            if (not hasShowdownRound):
                if (len(winners) > 1):
                    print ("Error: Hand Number " + ohh[GAME_NUMBER] + " appears to be missing a showdown round while having more than one winner.")
                elif (len(winners) == 0):
                    print ("Error: Hand Number " + ohh[GAME_NUMBER] + " appears there are no winners.")
                else:
                    round = {}
                    actionNumber = 0
                    round[ID] = (SHOWDOWN_ROUND_ID)
                    round[STREET] = makeNewRound[SHOW_DOWN]
                    round[CARDS] = []
                    round[ACTIONS] = []
                    action = {}
                    action[ACTION_NUMBER] = actionNumber
                    action[PLAYER_ID] = winners[0]
                    action[ACTION] = "Mucks Cards"
                    round[ACTIONS].append(action)
                ohh[ROUNDS].append(round)

        tables[table][OHH].append(ohh)


    # finally step through each table and produce an output file
    # with one OHH JSON object on a line
    # separated from one another by empty lines as specified by PT4 for import
    # UNLESS the -i or --indent flag was used in which case the JSON for
    # each OHH object will be indented for ease of reading and debugging
    for table in tables.keys():
        print("Table: " + table + " Processed hands:" +str(tables[table][COUNT]))
        print("\tLatest: " + tables[table][LATEST].strftime("%T %m/%d/%Y"))
        fileName = (config.get('DEFAULT',PREFIX) + tables[table][LATEST].strftime("-%Y-%m-%d-") +
                     re.sub("[<>\:\"\/\\\|\?\*]",'_', table ) + ".ohh")
        f = open(fileName, "w")
        for ohh in tables[table][OHH]:
            wrapped_ohh = {}
            wrapped_ohh[OHH] = ohh
            if (args.indent):
                f.write(json.dumps(wrapped_ohh, indent=4))
            else:
                f.write(json.dumps(wrapped_ohh))
            f.write("\n")
            f.write("\n")

        f.close()
