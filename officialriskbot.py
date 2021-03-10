import sqlite3
import numpy as np
import itertools
import pandas as pd
import trueskill
import scipy.special
import logging
import datetime
import re
import asyncio
import string
import secrets
import threading
import requests
import json

from collections import defaultdict

from time import time as gettime
from discord.ext import tasks

import discord
from discord.ext.commands import bot
from discord.ext import commands

db_path = "/home/tonymaroughi/Risk/risk-db-2.db"

# Boolean

#1v1

TURN = False
GAME = False
RUNNING = False
DRAFTING = False
STARTING = False

#2v2

TURN2 = False
GAME2 = False
RUNNING2 = False
DRAFTING2 = False
STARTING2 = False

#3v3

TURN3 = False
GAME3 = False
RUNNING3 = False
DRAFTING3 = False
STARTING3 = False

# Dictionaries

results = dict()
global_dict = dict()
LEAGUE = {}
joined_dic = {}
elo_dic = {}

# Lists and Variables

ID = 0
draw_votes = 0
won_votes = 0
lost_votes = 0
draw_votes2 = 0
won_votes2 = 0
lost_votes2 = 0
draw_votes3 = 0
won_votes3 = 0
lost_votes3 = 0
voting_list = []
solo_won = []
solo_lost = []
won_vote_names = []
lost_vote_names = []
draw_vote_names = []
team_won2 = []
team_lost2 = []
won_vote_names2 = []
lost_vote_names2 = []
draw_vote_names2 = []
team_won3 = []
team_lost3 = []
won_vote_names3 = []
lost_vote_names3 = []
draw_vote_names3 = []
PLAYERS = []
PLAYERS2 = []
PLAYERS3 = []
TEAMS = []
TEAMS2 = []
TEAMS3 = []
DRAFTING_ELOS = []
gametype_lobby = []
gametype_lobby2 = []
gametype_lobby3 = []
inactive_player_id = []
inactive_player_elo = []
warned = []
repeat_list = []
captain_team_one = []
captain_team_two = []
direct_messaging = []
no_score = []
no_score2 = []
no_score3 = []

# Logging

logger = logging.getLogger('discord')

# Logger.setLevel(logging.INFO)

handler = logging.FileHandler(filename='discord.log', encoding='utf-8', mode='a')
handler.setFormatter(logging.Formatter('%(asctime)s:%(levelname)s:%(name)s: %(message)s'))
logger.addHandler(handler)
main_elo = trueskill.TrueSkill(mu=1500, draw_probability=0, backend="mpmath", sigma=400, tau=10, beta=200)
main_elo.make_as_global()

# Channel ID's

na_lobby_channel = discord.Object(785009271317463091)
ones_channel = discord.Object(790313550270693396)
twos_channel = discord.Object(790313583484731422)
threes_channel = discord.Object(790313624395972668)
ffa_channel = discord.Object(784960892617490452)
admin_channel = discord.Object(785006670865498153) 
na_activity_channel = discord.Object(790313358816968715) 
na_leaderboard_channel = discord.Object(785234105968099409) 
na_draft_channel = discord.Object(785006588296560652) 
na_highlights_channel = discord.Object(784960959419908156)
na_announcements_channel = discord.Object(791741867845877771)
na_rules_channel = discord.Object(787070402768928819)
na_test_channel = discord.Object(787071010180169749)
na_general_channel = discord.Object(784960513435631670)
bot_spam_channel = discord.Object(787071010180169749)

# Discord Client

client = discord.Client()
bot_prefix = "!"
intents = discord.Intents.default()
intents.members = True
client = commands.Bot(command_prefix=bot_prefix, intents=intents)
# client.remove_command("help") #removes default help command
def erfc(x):
    """Complementary error function (via `http://bit.ly/zOLqbc`_)"""
    z = abs(x)
    t = 1. / (1. + z / 2.)
    r = t * np.math.exp(-z * z - 1.26551223 + t * (1.00002368 + t * (
        0.37409196 + t * (0.09678418 + t * (-0.18628806 + t * (
            0.27886807 + t * (-1.13520398 + t * (1.48851587 + t * (
                -0.82215223 + t * 0.17087277
            )))
        )))
    )))
    return 2. - r if x < 0 else r


def cdf(x, mu=0, sigma=1):
    """Cumulative distribution function"""
    return 0.5 * erfc(-(x - mu) / (sigma * np.math.sqrt(2)))

def win_probability(elo1, sigma1, elo2, sigma2):
    BETA=200
    deltaMu = elo1 - elo2
    sumSigma = sigma1**2 + sigma2**2
    rsss = sqrt(2* (BETA**2) + sumSigma)
    return cdf(deltaMu/rsss)
    
def safeName(name):
    """ Changes player's names that will mess up the discord leaderboard formatting to shitname """
    safe_name = ''.join(e for e in name if e.isalnum())
    if safe_name == '':
        safe_name = "Shitname"
    return safe_name


def find_user_by_name(ctx, name):
    conn = sqlite3.connect(db_path, uri=True)
    c = conn.cursor()
    out = None

    if len(name) == 0:
        # Tried without an input
        out = ctx.message.author
    else:
        # Test to see if it's a ping
        server = ctx.message.guild
        if name[0:2] == "<@":
            if name[2] == "!":
                player = server.get_member(name[3:-1])
            else:
                player = server.get_member(name[2:-1])
            if player is not None:
                out = player
        else:
            # Test to see if it's a username
            player = server.get_member_named(name)
            if player is not None:
                out = player
            else:
                # Check the database to see if it's a username
                conn = sqlite3.connect(db_path, uri=True)

                c = conn.cursor()
                c.execute("SELECT ID FROM players WHERE name LIKE ?", [name])
                result = c.fetchone()
                if result is not None:
                    player = server.get_member(result[0])
                    if player is not None:
                        out = player
                else:
                    # Check the database to see if it's LIKE a username
                    wildcard_name = name + "%"
                    c.execute("SELECT ID FROM players WHERE name LIKE ?", [wildcard_name])
                    result = c.fetchone()
                    if result is not None:
                        player = server.get_member(result[0])
                        if player is not None:
                            out = player
    conn.commit()
    conn.close()
    return out


def find_userid_by_name(ctx, name):
    conn = sqlite3.connect(db_path, uri=True)
    c = conn.cursor()
    out = None

    if len(name) == 0:
        # Tried without an input
        out = ctx.message.author.id
    else:
        # Test to see if it's a ping
        server = ctx.message.guild
        if name[0:2] == "<@":
            if name[2] == "!":
                player = get_member(name[3:-1])
            else:
                player = get_member(name[2:-1])
            if player is not None:
                out = player.id
        else:
            # Test to see if it's a username
            player = server.get_member_named(name)
            if player is not None:
                out = player.id
            else:
                # Check the database to see if it's a username
                c.execute("SELECT ID FROM players WHERE name LIKE ?", [name])
                result = c.fetchone()
                if result is not None:
                    out = result[0]
                else:
                    # Check the database to see if it's LIKE a username
                    wildcard_name = name + "%"
                    c.execute("SELECT ID FROM players WHERE name LIKE ?", [wildcard_name])
                    result = c.fetchone()
                    if result is not None:
                        out = result[0]
    conn.commit()
    conn.close()
    return out

@tasks.loop(seconds=10)
async def autokicktimer():

    global PLAYERS, joined_dic, elo_dic, repeat_list

    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    
    for player_id in PLAYERS:
        if gettime() - joined_dic[player_id] > 1020:
            lobby = client.get_channel(785009271317463091)
            user = client.get_user(player_id)
            c.execute("SELECT elo FROM PLAYERS WHERE ID = ?", [player_id])
            fetch = c.fetchone()
            player_elo = fetch[0]
            PLAYERS.remove(player_id)
            repeat_list.remove(player_id)
            await lobby.send(f"**{user.name} [{player_elo}]** has been kicked from the lobby for inactivity. **({str(len(set(PLAYERS)))})**")

    conn.close()

@tasks.loop(seconds=10)
async def timer():
    global PLAYERS, joined_dic, elo_dic, repeat_list

    conn = sqlite3.connect(db_path)
    c = conn.cursor()

    for player_id in PLAYERS:
        if gettime() - joined_dic[player_id] > 900 and player_id not in repeat_list:
            lobby = client.get_channel(785009271317463091)
            user = client.get_user(player_id)
            repeat_list.append(player_id)
            await lobby.send(f"{user.mention} Still around? (.here)")
        
    conn.close()

async def leaderboard_team(ctx):
    """ Updates the leaderboard channel """

    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    guild = ctx.guild
    leaderboard_channel = discord.utils.get(guild.channels, id=787070684106194954)
    leader_board = []
    i = 1
    msg = []  # Empty list to put all the messages in the log

    await leaderboard_channel.purge(limit=15)

    msg = "```\n"
    msg = msg + "{:<4}  {:<20}  {:<10}  {:<10}  {:<10} {:<10} {:<10}".format('RANK', 'NAME', 'WIN', 'LOSS', 'ELO', 'SIGMA',
                                                                      'WINRATE') + "" + "\n"

    for player in c.execute("SELECT name, win, loss, elo, record, id, lowest, sigma FROM players_team ORDER BY elo desc"):
        leader_board.append(player)

    for player in leader_board:
        total_games = int(player[1]) + int(player[2])
        win = int(player[1])
        if int(total_games) == 0:
            winrate = "0.0"
        else:
            winrate = float("{0:.2f}".format((int(win) / int(total_games)) * 100))

        if total_games > 0:

            if player[4] == None or player[3] > player[4]:
                c.execute("UPDATE players_team SET record = ? where ID = ?", [player[3], player[5]])

            msg = msg + "{:<4}  {:<20}  {:<10}  {:<10}  {:<10} {:<10} {:<10}".format('#' + str(i), safeName(player[0][:20]),
                                                                            player[1], player[2], int(round(player[3])), int(round(player[7])),
                                                                            str(winrate) + "%", (player[3])) + "" + "\n"
            c.execute("UPDATE players_team SET rank = ? WHERE ID = ?", [i,player[5]])
            i = i + 1
            if i % 10 == 0:
                await leaderboard_channel.send(msg + '```')
                msg = "```\n"
    c.execute("SELECT MAX(ELO), ID from PLAYERS_TEAM")
    player = c.fetchone()[1]
    member = guild.get_member(player)
    role = discord.utils.get(ctx.guild.roles, name="Rank 1 Team")
    await role.members[0].remove_roles(role)
    await member.add_roles(role)
    msg += "```"
    conn.commit()
    conn.close()
    await leaderboard_channel.send(msg)

async def leaderboard_solo(ctx):
    """ Updates the leaderboard channel """

    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    guild = ctx.guild
    leaderboard_channel = discord.utils.get(guild.channels, id=787070644427948142)
    leader_board = []
    i = 1
    msg = []  # Empty list to put all the messages in the log

    await leaderboard_channel.purge(limit=15)

    msg = "```\n"
    msg = msg + "{:<4}  {:<25}  {:<10} {:<10} {:<10}".format('RANK', 'NAME', 'ELO', 'SIGMA', 'TOTAL GAMES') + "" + "\n"

    for player in c.execute("SELECT name, win, loss, elo, record, id, lowest, sigma FROM players ORDER BY elo desc"):
        leader_board.append(player)

    for player in leader_board:
        member = guild.get_member(player[5])

        if member is None:
            names = player[0]

        if member is not None:
            if member.nick is None:
                names = member.name
        
            if member.nick is not None:
                names = member.nick  
                
        total_games = int(player[1]) + int(player[2])
        sigma = int(round(player[7]))

        if total_games > 19:

            if player[4] == None or player[3] > player[4]:
                c.execute("UPDATE players SET record = ? where ID = ?", [int(round(player[3])), player[5]])

            msg = msg + "{:<4}  {:<25}  {:<10}  {:<10}  {:<10}".format('#' + str(i), names,
                                                                            int(round(player[3])), int(round(player[7])), int(total_games)) + "" + "\n"
            c.execute("UPDATE players SET rank = ? WHERE ID = ?", [i,player[5]])
            i = i + 1
            if i % 10 == 0:
                await leaderboard_channel.send(msg + '```')
                msg = "```\n"
    c.execute("SELECT MAX(ELO), ID from PLAYERS")
    player = c.fetchone()[1]
    member = guild.get_member(player)
    role = discord.utils.get(ctx.guild.roles, name="Rank 1 Solo")
    await role.members[0].remove_roles(role)
    await member.add_roles(role)
    msg += "```"
    conn.commit()
    conn.close()
    await leaderboard_channel.send(msg)


async def printTeams(guild):
    """ Prints the drafted teams. """
    global TEAMS
    team_string = ""
    i = 1
    for team in TEAMS:
        for player in team:
            team_string += " " + player[1]
        lobby_channel = discord.utils.get(guild.channels, id=785009271317463091)
        await lobby_channel.send("Team " + str(i) + " : " + team_string)
        team_string = ""
        i = i + 1


# async def printPool(guild):
#
#     """ Prints the current draft pool."""
#
#     print(f"Drafting elos = {DRAFTING_ELOS}")
#
#     drafting_channel = discord.utils.get(guild.channels, id=750144623690776598)
#     i = 1
#     msg = "```\n"
#     msg = msg + "{:<5}  {:<25}  {:<5}".format('# ', 'NAME', 'ELO') + "" + "\n"
#     for player in DRAFTING_ELOS:
#         msg = msg + "{:<5}  {:<25}  {:<5}".format('#' + str(i), safeName(player[2]), str(player[1])) + "" + " \n"
#         i = i + 1
#         if i % 25 == 0:
#             await drafting_channel.send(msg + '```')
#             msg = "```\n"
#     msg += "```"
#     await drafting_channel.send(msg)

async def printPool(guild):
    drafting_channel = discord.utils.get(guild.channels, id=785006588296560652)

    player_string = []
    for player in DRAFTING_ELOS:
        player_string.append(f"{player[2]} [{player[1]}]")

    await drafting_channel.send('Players: ' + ', '.join(player_string))

@client.command(aliases=["pass"])
@commands.has_role("Captain")
async def skip(ctx):

    global TURN, GAME, PLAYERS, TEAMS, DRAFTING_ELOS, db_path

    t = ctx.author.id

    if ctx.channel.id == na_draft_channel.id:

        if TURN == str(t):
            print(TURN)

            TURN = str(TEAMS[0][0][0])
            print(TURN)

            player_string = []

            for player in DRAFTING_ELOS:
                player_string.append(f"{player[2]} [{player[1]}]")

            await ctx.send('Players: ' + ', '.join(player_string))
            await ctx.channel.send("<@" + str(TURN) + "> .draft player")


async def drafted(ctx):
    """ Starts the drafting process. """

    global TURN, GAME, PLAYERS, TEAMS, DRAFTING_ELOS, DRAFTING, db_path, captain_team_one, captain_team_two

    DRAFTING = True
    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    ELOS = []
    for t in PLAYERS:
        c.execute("SELECT elo,name FROM players WHERE ID = ?", [t])
        elo = c.fetchone()
        ELOS.append((t, int(elo[0]), elo[1]))
    ELOS.sort(key=lambda elos: elos[1], reverse=True)
    DRAFTING_ELOS = ELOS
    guild = discord.utils.get(client.guilds, id=784960512534380586)

    # add captains to teams
    TEAMS.append([(ELOS[0][0], ELOS[0][2], ELOS[0][1])])
    TEAMS.append([(ELOS[1][0], ELOS[1][2], ELOS[1][1])])

    captain_one = guild.get_member(ELOS[1][0])
    captain_two = guild.get_member(ELOS[0][0])
    TURN = str(TEAMS[1][0][0])
    turn_name = str(TEAMS[0][0][1])

    # add drafting roles
    role = discord.utils.get(guild.roles, name="Captain")
    await captain_one.add_roles(role)
    await captain_two.add_roles(role)

    draft_channel = discord.utils.get(guild.channels, id=785006588296560652)
    lobby_channel1 = discord.utils.get(guild.channels, id=785009271317463091)

    PLAYERS.remove(ELOS[0][0])
    PLAYERS.remove(ELOS[1][0])
    DRAFTING_ELOS.pop(0)
    DRAFTING_ELOS.pop(0)

    notestr = ""
    for t in PLAYERS:
        notestr += "<@" + str(t) + ">, "

    notestr += captain_one.mention + "," + captain_two.mention

    await draft_channel.send("Draft started.")
    await draft_channel.send(notestr + "\nCaptains: " + captain_one.name + ", " + captain_two.name + "")
    captain_team_one.append(captain_one.name)
    captain_team_two.append(captain_two.name)

    await printPool(guild)

    await draft_channel.send("<@" + str(TURN) + "> .draft player")

    last_len = 2
    counter = 0
    while len(TEAMS[0]) < 4 or len(TEAMS[1]) < 4:
        await asyncio.sleep(5)
        if len(TEAMS[0]) + len(TEAMS[1]) == last_len:
            counter = counter + 1
            if counter > 60:
                await captain_one.remove_roles(role)
                await captain_two.remove_roles(role)
                DRAFTING = False
                return None
        else:
            last_len = len(TEAMS[0]) + len(TEAMS[1])
            counter = 0

        if len(TEAMS[0]) is 3 and len(DRAFTING_ELOS) is 1:
            await draft_channel.send("Draft finished.")
            return

        elif len(TEAMS[1]) is 3 and len(DRAFTING_ELOS) is 1:
            await draft_channel.send("Draft finished.")
            return

    await captain_one.remove_roles(role)
    await captain_two.remove_roles(role)
    await draft_channel.send("Draft finished.")


async def clearAll():
    global TURN, GAME, PLAYERS, TEAMS, RUNNING

    TURN = False
    TEAMS = []
    PLAYERS = []
    GAME = False
    RUNNING = False
    CUSTOM_LOCK = False


def isName(memberName, member):
    name = member.display_name
    name = name.upper()
    pattern = re.compile('[\W_]+')
    if memberName.upper() in pattern.sub('', name).upper():
        return True
    else:
        return False


@client.event
async def on_ready():

    global PLAYERS, joined_dic, GAME, RUNNING, results, TURN, TEAMS, LEAGUE, DRAFTING_ELOS, STARTING, DRAFTING, gametype_lobby

    # conn = sqlite3.connect(db_path)
    # c = conn.cursor()

    # try:
            
    #     c.execute("SELECT PLAYERS, joined_dic, GAME, RUNNING, results, TURN, TEAMS, LEAGUE, DRAFTING_ELOS, STARTING, DRAFTING, gametype_lobby from RESTART")
    #     fetch = c.fetchone()
    #     PLAYERS = fetch[0]
    #     joined_dic = fetch[1]
    #     GAME = fetch[2]
    #     RUNNING = fetch[3]
    #     TURN = fetch[5]
    #     TEAMS = fetch[6]
    #     LEAGUE = fetch[7]
    #     DRAFTING_ELOS = fetch[8]
    #     STARTING = fetch[9]
    #     DRAFTING = fetch[10]
    #     gametype_lobby = fetch[11]
    #     c.execute("UPDATE restart SET PLAYERS = NULL")
    #     c.execute("UPDATE restart SET joined_dic = NULL")
    #     c.execute("UPDATE restart SET GAME = NULL")
    #     c.execute("UPDATE restart SET RUNNING = NULL")
    #     c.execute("UPDATE restart SET TURN = NULL")
    #     c.execute("UPDATE restart SET TEAMS = NULL")
    #     c.execute("UPDATE restart SET LEAGUE = NULL")
    #     c.execute("UPDATE restart SET DRAFTING_ELOS = NULL")
    #     c.execute("UPDATE restart SET STARTING = NULL")
    #     c.execute("UPDATE restart SET DRAFTING = NULL")
    #     c.execute("UPDATE restart SET gametype_lobby = NULL")

    # except:

    #     print("There was an error loading variables from database or bot wasn't shut down using command.")

    # else:
            
    # conn.commit()
    # conn.close()
    print('We have logged in as {0.user}'.format(client))
    status = discord.Activity(name='Warcraft III', type=1)
    await client.change_presence(activity=status)
    print(discord.__version__)
    return


# @client.command()
# @commands.cooldown(1, 5, commands.BucketType.user)
# async def lowest(ctx):
#     '''Shows lowest ELO of player.'''

#     global joined_dic

#     if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

#         x = ctx.author.id
#         joined_dic[x] = gettime()
#         t = ctx.author.id
#         conn = sqlite3.connect(db_path)
#         c = conn.cursor()
#         c.execute("SELECT lowest, name, streak FROM players WHERE ID = ?", [t])
#         sql = c.fetchone()
#         lowest = sql[0]
#         name = sql[1]
#         await ctx.send(f"**{name}**'s lowest elo is **{lowest}**.")
#         conn.close()

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def register(ctx, member: discord.Member=None):
    '''Registers a user into the player database.'''

    global db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
            
        conn = sqlite3.connect(db_path)

        c = conn.cursor()

        B = ctx.message.author.name

        A = ctx.message.author.id

        mod_role = discord.utils.get(ctx.guild.roles, name="League Admin")

        L = ctx.author

        date = datetime.datetime.now()

        role = discord.utils.get(ctx.guild.roles, name="League")

        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"

        if member == None:
                
            await L.add_roles(role)
            await ctx.channel.send('Added player role.')

        if member:

            if mod_role in ctx.author.roles:

                c.execute("SELECT elo FROM players WHERE ID = ?", [member.id])
                row = c.fetchone()
                if row == None:
                    c.execute('INSERT INTO players VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                            [member.id, member.name, "Empty", date, str(profile)])
                    c.execute("INSERT INTO warnings VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [member.id,member.name])
                    await ctx.channel.send(f'Registered {member.name}.')
                    role = discord.utils.get(ctx.guild.roles, name="League")
                    await member.add_roles(role)
                
                else: 
                    await ctx.send("You have already registered.")

        conn.commit()

    if ctx.channel.id == twos_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
            
        conn = sqlite3.connect(db_path)

        c = conn.cursor()

        B = ctx.message.author.name

        A = ctx.message.author.id

        mod_role = discord.utils.get(ctx.guild.roles, name="League Admin")

        L = ctx.author

        date = datetime.datetime.now()

        role = discord.utils.get(ctx.guild.roles, name="League")

        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"

        if member == None:
                
            await L.add_roles(role)
            await ctx.channel.send('Added player role.')

        if member:

            if mod_role in ctx.author.roles:

                c.execute("SELECT elo FROM players_team WHERE ID = ?", [member.id])
                row = c.fetchone()
                if row == None:
                    c.execute('INSERT INTO players_team VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                            [member.id, member.name, "Empty", date, str(profile)])
                    c.execute("INSERT INTO warnings2 VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [member.id,member.name])
                    await ctx.channel.send(f'Registered {member.name}.')
                    role = discord.utils.get(ctx.guild.roles, name="League")
                    await member.add_roles(role)
                
                else: 
                    await ctx.send("You have already registered.")

        conn.commit()

    if ctx.channel.id == threes_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
            
        conn = sqlite3.connect(db_path)

        c = conn.cursor()

        B = ctx.message.author.name

        A = ctx.message.author.id

        mod_role = discord.utils.get(ctx.guild.roles, name="League Admin")

        L = ctx.author

        date = datetime.datetime.now()

        role = discord.utils.get(ctx.guild.roles, name="League")

        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"

        if member == None:
                
            await L.add_roles(role)
            await ctx.channel.send('Added player role.')

        if member:

            if mod_role in ctx.author.roles:

                c.execute("SELECT elo FROM players_team WHERE ID = ?", [member.id])
                row = c.fetchone()
                if row == None:
                    c.execute('INSERT INTO players_team VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                            [member.id, member.name, "Empty", date, str(profile)])
                    c.execute("INSERT INTO warnings3 VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [member.id,member.name])
                    await ctx.channel.send(f'Registered {member.name}.')
                    role = discord.utils.get(ctx.guild.roles, name="League")
                    await member.add_roles(role)
                
                else: 
                    await ctx.send("You have already registered.")

        conn.commit()


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def unregister(ctx):

    """Removes banjo role."""

    global joined_dic

    if ctx.channel.id == ones_channel.id or ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:
                
        t = ctx.author
        joined_dic[t] = gettime()
        banjo_role = discord.utils.get(ctx.guild.roles, name="League")
        await t.remove_roles(banjo_role)
        await ctx.send("Banjo role removed.")


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def lobby(ctx):
    '''Show's the current players in the lobby.'''

    global PLAYERS, PLAYERS2, PLAYERS3, GAME, GAME2, GAME3, db_path, gametype_lobby, gametype_lobby2, gametype_lobby3, TEAMS, TEAMS2, TEAMS3, DRAFTING_ELOS

    conn = sqlite3.connect(db_path, uri=True)

    c = conn.cursor()

    if ctx.message.channel.id == threes_channel.id:
        if GAME3:
            PLAYERS3 = list(set(PLAYERS3))
            NAMES = []
            for t in PLAYERS3:
                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            tup = tuple(PLAYERS3)    
            if len(set(PLAYERS3)) > 1:
                sql = "select name from players_team where id IN {}".format(tup)
                sql += " ORDER BY elo desc LIMIT 2"
                c.execute((sql))

            elif len(PLAYERS) == 1:
                sql = "select name from players_team where id = ?"
                c.execute((sql), [tup[0]])
            data = c.fetchall()
            strCaptainsList = "Projected Captains: **"
            for d in data:
                strCaptainsList += "  " + str(d[0])

            if len(set(PLAYERS3)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby3[0]) + ") (" + str(len(set(PLAYERS3))) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "

                await ctx.channel.send(lobbystr)

                if gametype_lobby3[0] == "draft":
                    await ctx.channel.send(strCaptainsList + "**")

            elif ctx.message.channel.id == threes_channel.id:
                await ctx.channel.send("There is no lobby active.")

        if len(PLAYERS3) == 0:
            await ctx.channel.send("There is no lobby active.")

        if DRAFTING3:
            PLAYERS3 = list(set(PLAYERS3))

            NAMES = []
            for t in PLAYERS3:
                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            if len(set(PLAYERS3)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby3[0]) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "
                CAPTAIN_ONE = TEAMS3[0][0][1]
                CAPTAIN_TWO = TEAMS3[1][0][1]
                lobbystr += CAPTAIN_ONE + " **[" + str(TEAMS3[0][0][2]) + "**] " + CAPTAIN_TWO + " **[" + str(TEAMS3[1][0][2]) + "]**"

                await ctx.channel.send(lobbystr)

    if ctx.message.channel.id == twos_channel.id:
        if GAME2:
            PLAYERS2 = list(set(PLAYERS2))
            NAMES = []
            for t in PLAYERS2:
                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            tup = tuple(PLAYERS2)    
            if len(set(PLAYERS2)) > 1:
                sql = "select name from players_team where id IN {}".format(tup)
                sql += " ORDER BY elo desc LIMIT 2"
                c.execute((sql))

            elif len(PLAYERS2) == 1:
                sql = "select name from players_team where id = ?"
                c.execute((sql), [tup[0]])
            data = c.fetchall()
            strCaptainsList = "Projected Captains: **"
            for d in data:
                strCaptainsList += "  " + str(d[0])

            if len(set(PLAYERS2)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby2[0]) + ") (" + str(len(set(PLAYERS2))) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "

                await ctx.channel.send(lobbystr)

                if gametype_lobby2[0] == "draft":
                    await ctx.channel.send(strCaptainsList + "**")

            elif ctx.message.channel.id == twos_channel.id:
                await ctx.channel.send("There is no lobby active.")

        if len(PLAYERS2) == 0:
            await ctx.channel.send("There is no lobby active.")

        if DRAFTING2:
            PLAYERS2 = list(set(PLAYERS2))

            NAMES = []
            for t in PLAYERS2:
                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            if len(set(PLAYERS2)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby2[0]) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "
                CAPTAIN_ONE = TEAMS2[0][0][1]
                CAPTAIN_TWO = TEAMS2[1][0][1]
                lobbystr += CAPTAIN_ONE + " **[" + str(TEAMS2[0][0][2]) + "**] " + CAPTAIN_TWO + " **[" + str(TEAMS2[1][0][2]) + "]**"

                await ctx.channel.send(lobbystr)

    if ctx.message.channel.id == ones_channel.id:
        if GAME:
            PLAYERS = list(set(PLAYERS))
            NAMES = []
            for t in PLAYERS:
                c.execute("SELECT name, elo FROM players WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            tup = tuple(PLAYERS)    
            if len(set(PLAYERS)) > 1:
                sql = "select name from players where id IN {}".format(tup)
                sql += " ORDER BY elo desc LIMIT 2"
                c.execute((sql))

            elif len(PLAYERS) == 1:
                sql = "select name from players where id = ?"
                c.execute((sql), [tup[0]])
            data = c.fetchall()
            strCaptainsList = "Projected Captains: **"
            for d in data:
                strCaptainsList += "  " + str(d[0])

            if len(set(PLAYERS)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby[0]) + ") (" + str(len(set(PLAYERS))) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "

                await ctx.channel.send(lobbystr)

                if gametype_lobby[0] == "draft":
                    await ctx.channel.send(strCaptainsList + "**")

            elif ctx.message.channel.id == ones_channel.id:
                await ctx.channel.send("There is no lobby active.")

        if len(PLAYERS) == 0:
            await ctx.channel.send("There is no lobby active.")

        if DRAFTING:
            PLAYERS = list(set(PLAYERS))

            NAMES = []
            for t in PLAYERS:
                c.execute("SELECT name, elo FROM players WHERE ID = ?", [t])
                result = c.fetchone()
                name = result[0]
                pts = int(round(result[1]))
                NAMES.append(name + " **[" + str(pts) + "]**")

            if len(set(PLAYERS)) > 0:
                lobbystr = f"Current Lobby **(" + str(gametype_lobby[0]) + ")**: "
                for t in NAMES:
                    lobbystr += t + " "
                CAPTAIN_ONE = TEAMS[0][0][1]
                CAPTAIN_TWO = TEAMS[1][0][1]
                lobbystr += CAPTAIN_ONE + " **[" + str(TEAMS[0][0][2]) + "**] " + CAPTAIN_TWO + " **[" + str(TEAMS[1][0][2]) + "]**"

                await ctx.channel.send(lobbystr)

    conn.close()


@client.command(aliases=["kill"])
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def end(ctx):
    '''Ends the current lobby.'''

    global PLAYERS, PLAYERS2, PLAYERS3, GAME, GAME2, GAME3, RUNNING, RUNNING2, RUNNING3, DRAFTING

    if ctx.channel.id == ones_channel.id:

        t = ctx.message.author.id

        if RUNNING:
            PLAYERS = []
            RUNNING = False
            GAME = False
            DRAFTING = False

        await ctx.channel.send("Lobby ended.")

    if ctx.channel.id == twos_channel.id:

        t = ctx.message.author.id

        if RUNNING2:
            PLAYERS2 = []
            RUNNING2 = False
            GAME2 = False
            DRAFTING2 = False

        await ctx.channel.send("Lobby ended.")

    if ctx.channel.id == threes_channel.id:

        t = ctx.message.author.id

        if RUNNING3:
            PLAYERS3 = []
            RUNNING3 = False
            GAME3 = False
            DRAFTING3 = False

        await ctx.channel.send("Lobby ended.")

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('Dev')
async def forcejoinall(ctx):
    '''Forcejoins 7 players into the lobby for testing'''

    global PLAYERS, GAME, RUNNING, db_path

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:
            
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()

        player1 = 102475732378193920
        player2 = 341306490071810050
        player3 = 222886535631077378
        player4 = 229094474297376770
        player5 = 565326927976726538
        player6 = 676645353327427600
        player7 = 641160452247781397

        c.execute("SELECT name FROM players WHERE ID = ?", [player1])
        c.execute("SELECT name FROM players WHERE ID = ?", [player2])
        c.execute("SELECT name FROM players WHERE ID = ?", [player3])
        c.execute("SELECT name FROM players WHERE ID = ?", [player4])
        c.execute("SELECT name FROM players WHERE ID = ?", [player5])
        c.execute("SELECT name FROM players WHERE ID = ?", [player6])
        c.execute("SELECT name FROM players WHERE ID = ?", [player7])
        user = c.fetchone()
        name = user[0]

        if GAME:
            PLAYERS = list(set(PLAYERS))
            PLAYERS.append(player1)
            PLAYERS.append(player2)
            PLAYERS.append(player3)
            PLAYERS.append(player4)
            PLAYERS.append(player5)
            PLAYERS.append(player6)
            PLAYERS.append(player7)

            await ctx.channel.send("Forced a full lobby.")

        conn.commit()
        conn.close()

@client.command()
async def search(ctx, gn):

    """Searches through Warcraft III gamelist."""
    
    result = requests.get('https://api.wc3stats.com/gamelist')

    gamelist = result.json()
    

    games = []
    for game in gamelist ['body']:
        if re.search(gn, game['name'], re.IGNORECASE):
            slots_taken = game['slotsTaken']
            slots_total = game['slotsTotal']
            emb = (discord.Embed(description='**Server:** [' + game['server'] + '] /n **Game Name:** ' + game['name'] + '/n **Slots:** (' + str(slots_taken) + '/' + str(slots_total) + ')' '/n **Host:** [' + game['host'] + ']', colour=0x3DF27))
            games.append('[' + game['server'] + '] ' + game['name'] + ' (' + str(slots_taken) + '/' + str(slots_total) + ')' ' [' + game['host'] + ']')

    if len(games) <= 0:
            await ctx.channel.send("No games found.")

    else:
        for game in games:
            await ctx.channel.send(game)

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def dm(ctx):

    """Add or remove direct messaging notifications for games."""

    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    t = ctx.author.id
    n = ctx.author.name
    c.execute("SELECT name FROM DM WHERE ID = ?", [t])
    check = c.fetchone()

    if check is None:
        
        c.execute("INSERT into DM VALUES (?,?)", [t,n])
        await ctx.send("Enabled direct messaging.")
        conn.commit()
        conn.close()
    
    if check is not None:
    
        c.execute("DELETE from DM WHERE ID = ?", [t])
        await ctx.send("Disabled direct messaging.")
        conn.commit()
        conn.close()

@client.command()
async def last(ctx, player=None):

    """Displays 5 previous games played statistics for user."""

    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    t = ctx.author.id
    n = ctx.author.name
    if player is not None:
        player = find_userid_by_name(ctx, player)
        c.execute("SELECT * FROM GAMES WHERE (P1 == ? or P2 == ? or P3 == ? or P4 == ? or P5 == ? or P6 == ? or P7 == ? or P8 == ?) AND (S1 != S2) ORDER BY ID DESC LIMIT 5", [player,player,player,player,player,player,player,player])
        rows = c.fetchall()
    if player is None:
        c.execute("SELECT * FROM GAMES WHERE (P1 == ? or P2 == ? or P3 == ? or P4 == ? or P5 == ? or P6 == ? or P7 == ? or P8 == ?) AND (S1 != S2) ORDER BY ID DESC LIMIT 5", [t,t,t,t,t,t,t,t])
        rows = c.fetchall()
    
    if len(rows) == 5:

        gamestr = []
        
        game1 = rows[0]
        game1id = game1[0]
        game1player1 = game1[1]
        game1player2 = game1[2]
        game1player3 = game1[3]
        game1player4 = game1[4]
        game1player5 = game1[5]
        game1player6 = game1[6]
        game1player7 = game1[7]
        game1player8 = game1[8]
        game1team1score = game1[9]
        game1team2score = game1[10]
        game1date = game1[13]

        game_1_team_1 = []
        game_1_team_2 = []

        game_1_team_1.append(game1player1)
        game_1_team_1.append(game1player2)
        game_1_team_1.append(game1player3)
        game_1_team_1.append(game1player4)

        game_1_team_2.append(game1player5)
        game_1_team_2.append(game1player6)
        game_1_team_2.append(game1player7)
        game_1_team_2.append(game1player8)

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player1])
        fetch1 = c.fetchone()
        name1 = fetch1[0]
        elo1 = fetch1[1]
        g1p1name = name1
        g1p1elo = elo1
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player2])
        fetch2 = c.fetchone()
        name2 = fetch2[0]
        elo2 = fetch2[1]
        g1p2name = name2
        g1p2elo = elo2
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player3])
        fetch3 = c.fetchone()
        name3 = fetch3[0]
        elo3 = fetch3[1]
        g1p3name = name3
        g1p3elo = elo3
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player4])
        fetch4 = c.fetchone()
        name4 = fetch4[0]
        elo4 = fetch4[1]
        g1p4name = name4
        g1p4elo = elo4
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player5])
        fetch5 = c.fetchone()
        name5 = fetch5[0]
        elo5 = fetch5[1]
        g1p5name = name5
        g1p5elo = elo5
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player6])
        fetch6 = c.fetchone()
        name6 = fetch6[0]
        elo6 = fetch6[1]
        g1p6name = name6
        g1p6elo = elo6
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player7])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g1p7name = name7
        g1p7elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player8])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g1p8name = name8
        g1p8elo = elo8

        if player is None:
                
            if t in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if t in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if t in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        if player is not None:

            if player in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if player in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if player in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        gamestr = f"**Game #{game1id}:** ({game1date})\nTeam 1 {game1team1score}: {g1p1name} [{g1p1elo}], {g1p2name} [{g1p2elo}], {g1p3name} [{g1p3elo}], {g1p4name} [{g1p4elo}]\nTeam 2 {game1team2score}: {g1p5name} [{g1p5elo}], {g1p6name} [{g1p6elo}], {g1p7name} [{g1p7elo}], {g1p8name} [{g1p8elo}]\n"

        game2 = rows[1]
        game2id = game2[0]
        game2player1 = game2[1]
        game2player2 = game2[2]
        game2player3 = game2[3]
        game2player4 = game2[4]
        game2player5 = game2[5]
        game2player6 = game2[6]
        game2player7 = game2[7]
        game2player8 = game2[8]
        game2team1score = game2[9]
        game2team2score = game2[10]
        game2date = game2[13]

        game_2_team_1 = []
        game_2_team_2 = []

        game_2_team_1.append(game2player1)
        game_2_team_1.append(game2player2)
        game_2_team_1.append(game2player3)
        game_2_team_1.append(game2player4)

        game_2_team_2.append(game2player5)
        game_2_team_2.append(game2player6)
        game_2_team_2.append(game2player7)
        game_2_team_2.append(game2player8)

        if player is None:
                

            if t in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if t in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if t in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        if player is not None:

            if player in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if player in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if player in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player1])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g2p1name = name7
        g2p1elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player2])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g2p2name = name8
        g2p2elo = elo8
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player3])
        fetch9 = c.fetchone()
        name9 = fetch9[0]
        elo9 = fetch9[1]
        g2p3name = name9
        g2p3elo = elo9
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player4])
        fetch10 = c.fetchone()
        name10 = fetch10[0]
        elo10 = fetch10[1]
        g2p4name = name10
        g2p4elo = elo10
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player5])
        fetch11 = c.fetchone()
        name11 = fetch11[0]
        elo11 = fetch11[1]
        g2p5name = name11
        g2p5elo = elo11
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player6])
        fetch12 = c.fetchone()
        name12 = fetch12[0]
        elo12 = fetch12[1]
        g2p6name = name12
        g2p6elo = elo12
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player7])
        fetch13 = c.fetchone()
        name13 = fetch13[0]
        elo13 = fetch13[1]
        g2p7name = name13
        g2p7elo = elo13
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player8])
        fetch14 = c.fetchone()
        name14 = fetch14[0]
        elo14 = fetch14[1]
        g2p8name = name14
        g2p8elo = elo14

        gamestr += f"**Game #{game2id}:** ({game2date})\nTeam 1 {game2team1score}: {g2p1name} [{g2p1elo}], {g2p2name} [{g2p2elo}], {g2p3name} [{g2p3elo}], {g2p4name} [{g2p4elo}]\nTeam 2 {game2team2score}: {g2p5name} [{g2p5elo}], {g2p6name} [{g2p6elo}], {g2p7name} [{g2p7elo}], {g2p8name} [{g2p8elo}]\n"

        game3 = rows[2]
        game3id = game3[0]
        game3player1 = game3[1]
        game3player2 = game3[2]
        game3player3 = game3[3]
        game3player4 = game3[4]
        game3player5 = game3[5]
        game3player6 = game3[6]
        game3player7 = game3[7]
        game3player8 = game3[8]
        game3team1score = game3[9]
        game3team2score = game3[10]
        game3date = game3[13]

        game_3_team_1 = []
        game_3_team_2 = []

        game_3_team_1.append(game3player1)
        game_3_team_1.append(game3player2)
        game_3_team_1.append(game3player3)
        game_3_team_1.append(game3player4)

        game_3_team_2.append(game3player5)
        game_3_team_2.append(game3player6)
        game_3_team_2.append(game3player7)
        game_3_team_2.append(game3player8)

        if player is None:

            if t in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if t in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if t in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if t in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        if player is not None:

            if player in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if player in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if player in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if player in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player1])
        fetch15 = c.fetchone()
        name15 = fetch15[0]
        elo15 = fetch15[1]
        g3p1name = name15
        g3p1elo = elo15
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player2])
        fetch16 = c.fetchone()
        name16 = fetch16[0]
        elo16 = fetch16[1]
        g3p2name = name16
        g3p2elo = elo16
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player3])
        fetch17 = c.fetchone()
        name17 = fetch17[0]
        elo17 = fetch17[1]
        g3p3name = name17
        g3p3elo = elo17
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player4])
        fetch18 = c.fetchone()
        name18 = fetch18[0]
        elo18 = fetch18[1]
        g3p4name = name18
        g3p4elo = elo18
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player5])
        fetch19 = c.fetchone()
        name19 = fetch19[0]
        elo19 = fetch19[1]
        g3p5name = name19
        g3p5elo = elo19
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player6])
        fetch20 = c.fetchone()
        name20 = fetch20[0]
        elo20 = fetch20[1]
        g3p6name = name20
        g3p6elo = elo20
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player7])
        fetch21 = c.fetchone()
        name21 = fetch21[0]
        elo21 = fetch21[1]
        g3p7name = name21
        g3p7elo = elo21
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player8])
        fetch22 = c.fetchone()
        name22 = fetch22[0]
        elo22 = fetch22[1]
        g3p8name = name22
        g3p8elo = elo22

        gamestr += f"**Game #{game3id}:** ({game3date})\nTeam 1 {game3team1score}: {g3p1name} [{g3p1elo}], {g3p2name} [{g3p2elo}], {g3p3name} [{g3p3elo}], {g3p4name} [{g3p4elo}]\nTeam 2 {game3team2score}: {g3p5name} [{g3p5elo}], {g3p6name} [{g3p6elo}], {g3p7name} [{g3p7elo}], {g3p8name} [{g3p8elo}]\n"

        game4 = rows[3]
        game4id = game4[0]
        game4player1 = game4[1]
        game4player2 = game4[2]
        game4player3 = game4[3]
        game4player4 = game4[4]
        game4player5 = game4[5]
        game4player6 = game4[6]
        game4player7 = game4[7]
        game4player8 = game4[8]
        game4team1score = game4[9]
        game4team2score = game4[10]
        game4date = game4[13]

        game_4_team_1 = []
        game_4_team_2 = []

        game_4_team_1.append(game4player1)
        game_4_team_1.append(game4player2)
        game_4_team_1.append(game4player3)
        game_4_team_1.append(game4player4)

        game_4_team_2.append(game4player5)
        game_4_team_2.append(game4player6)
        game_4_team_2.append(game4player7)
        game_4_team_2.append(game4player8)

        if player is None:
                
            if t in game_4_team_1 and game4team2score > game4team1score:

                    game4team2score = "(winner)"
                    game4team1score = "**(loser)**"

            if t in game_4_team_1 and game4team1score > game4team2score:
                
                    game4team1score = "**(winner)**"
                    game4team2score = "(loser)"

            if t in game_4_team_2 and game4team2score > game4team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if t in game_4_team_2 and game4team1score > game4team2score:
                
                    game4team1score = "(winner)"
                    game4team2score = "**(loser)**"

        if player is not None:

            if player in game_4_team_1 and game4team2score > game4team1score:

                    game4team2score = "(winner)"
                    game4team1score = "**(loser)**"

            if player in game_4_team_1 and game4team1score > game4team2score:
                
                    game4team1score = "**(winner)**"
                    game4team2score = "(loser)"

            if player in game_4_team_2 and game4team2score > game4team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if player in game_4_team_2 and game4team1score > game4team2score:
                
                    game4team1score = "(winner)"
                    game4team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player1])
        fetch23 = c.fetchone()
        name23 = fetch23[0]
        elo23 = fetch23[1]
        g4p1name = name23
        g4p1elo = elo23
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player2])
        fetch24 = c.fetchone()
        name24 = fetch24[0]
        elo24 = fetch24[1]
        g4p2name = name24
        g4p2elo = elo24
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player3])
        fetch25 = c.fetchone()
        name25 = fetch25[0]
        elo25 = fetch25[1]
        g4p3name = name25
        g4p3elo = elo25
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player4])
        fetch26 = c.fetchone()
        name26 = fetch26[0]
        elo26 = fetch26[1]
        g4p4name = name26
        g4p4elo = elo26
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player5])
        fetch27 = c.fetchone()
        name27 = fetch27[0]
        elo27 = fetch27[1]
        g4p5name = name27
        g4p5elo = elo27
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player6])
        fetch28 = c.fetchone()
        name28 = fetch28[0]
        elo28 = fetch28[1]
        g4p6name = name28
        g4p6elo = elo28
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player7])
        fetch29 = c.fetchone()
        name29 = fetch29[0]
        elo29 = fetch29[1]
        g4p7name = name29
        g4p7elo = elo29
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player8])
        fetch30 = c.fetchone()
        name30 = fetch30[0]
        elo30 = fetch30[1]
        g4p8name = name30
        g4p8elo = elo30

        gamestr += f"**Game #{game4id}:** ({game4date})\nTeam 1 {game4team1score}: {g4p1name} [{g4p1elo}], {g4p2name} [{g4p2elo}], {g4p3name} [{g4p3elo}], {g4p4name} [{g4p4elo}]\nTeam 2 {game4team2score}: {g4p5name} [{g4p5elo}], {g4p6name} [{g4p6elo}], {g4p7name} [{g4p7elo}], {g4p8name} [{g4p8elo}]\n"

        game5 = rows[4]
        game5id = game5[0]
        game5player1 = game5[1]
        game5player2 = game5[2]
        game5player3 = game5[3]
        game5player4 = game5[4]
        game5player5 = game5[5]
        game5player6 = game5[6]
        game5player7 = game5[7]
        game5player8 = game5[8]
        game5team1score = game5[9]
        game5team2score = game5[10]
        game5date = game5[13]

        game_5_team_1 = []  
        game_5_team_2 = []

        game_5_team_1.append(game5player1)
        game_5_team_1.append(game5player2)
        game_5_team_1.append(game5player3)
        game_5_team_1.append(game5player4)

        game_5_team_2.append(game5player5)
        game_5_team_2.append(game5player6)
        game_5_team_2.append(game5player7)
        game_5_team_2.append(game5player8)

        if player is None:
                
            if t in game_5_team_1 and game5team2score > game5team1score:

                    game5team2score = "(winner)"
                    game5team1score = "**(loser)**"

            if t in game_5_team_1 and game5team1score > game5team2score:
                
                    game5team1score = "**(winner)**"
                    game5team2score = "(loser)"

            if t in game_5_team_2 and game5team2score > game5team1score:

                    game5team2score = "**(winner)**"
                    game5team1score = "(loser)"

            if t in game_5_team_2 and game5team1score > game5team2score:
                
                    game5team1score = "(winner)"
                    game5team2score = "**(loser)**"

        if player is not None:
                
            if player in game_5_team_1 and game5team2score > game5team1score:

                    game5team2score = "(winner)"
                    game5team1score = "**(loser)**"

            if player in game_5_team_1 and game5team1score > game5team2score:
                
                    game5team1score = "**(winner)**"
                    game5team2score = "(loser)"

            if player in game_5_team_2 and game5team2score > game5team1score:

                    game5team2score = "**(winner)**"
                    game5team1score = "(loser)"

            if player in game_5_team_2 and game5team1score > game5team2score:
                
                    game5team1score = "(winner)"
                    game5team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player1])
        fetch31 = c.fetchone()
        name31 = fetch31[0]
        elo31 = fetch31[1]
        g5p1name = name31
        g5p1elo = elo31
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player2])
        fetch32 = c.fetchone()
        name32 = fetch32[0]
        elo32 = fetch32[1]
        g5p2name = name32
        g5p2elo = elo32
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player3])
        fetch33 = c.fetchone()
        name33 = fetch33[0]
        elo33 = fetch33[1]
        g5p3name = name33
        g5p3elo = elo33
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player4])
        fetch34 = c.fetchone()
        name34 = fetch34[0]
        elo34 = fetch34[1]
        g5p4name = name34
        g5p4elo = elo34
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player5])
        fetch35 = c.fetchone()
        name35 = fetch35[0]
        elo35 = fetch35[1]
        g5p5name = name35
        g5p5elo = elo35
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player6])
        fetch36 = c.fetchone()
        name36 = fetch36[0]
        elo36 = fetch36[1]
        g5p6name = name36
        g5p6elo = elo36
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player7])
        fetch37 = c.fetchone()
        name37 = fetch37[0]
        elo37 = fetch37[1]
        g5p7name = name37
        g5p7elo = elo37
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game5player8])
        fetch38 = c.fetchone()
        name38 = fetch38[0]
        elo38 = fetch38[1]
        g5p8name = name38
        g5p8elo = elo38

        gamestr += f"**Game #{game5id}:** ({game5date})\nTeam 1 {game5team1score}: {g5p1name} [{g5p1elo}], {g5p2name} [{g5p2elo}], {g5p3name} [{g5p3elo}], {g5p4name} [{g5p4elo}]\nTeam 2 {game5team2score}: {g5p5name} [{g5p5elo}], {g5p6name} [{g5p6elo}], {g5p7name} [{g5p7elo}], {g5p8name} [{g5p8elo}]"

        await ctx.send(gamestr)

        conn.close()

    if len(rows) == 4:

        gamestr = []
        
        game1 = rows[0]
        game1id = game1[0]
        game1player1 = game1[1]
        game1player2 = game1[2]
        game1player3 = game1[3]
        game1player4 = game1[4]
        game1player5 = game1[5]
        game1player6 = game1[6]
        game1player7 = game1[7]
        game1player8 = game1[8]
        game1team1score = game1[9]
        game1team2score = game1[10]
        game1date = game1[13]

        game_1_team_1 = []
        game_1_team_2 = []

        game_1_team_1.append(game1player1)
        game_1_team_1.append(game1player2)
        game_1_team_1.append(game1player3)
        game_1_team_1.append(game1player4)

        game_1_team_2.append(game1player5)
        game_1_team_2.append(game1player6)
        game_1_team_2.append(game1player7)
        game_1_team_2.append(game1player8)

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player1])
        fetch1 = c.fetchone()
        name1 = fetch1[0]
        elo1 = fetch1[1]
        g1p1name = name1
        g1p1elo = elo1
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player2])
        fetch2 = c.fetchone()
        name2 = fetch2[0]
        elo2 = fetch2[1]
        g1p2name = name2
        g1p2elo = elo2
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player3])
        fetch3 = c.fetchone()
        name3 = fetch3[0]
        elo3 = fetch3[1]
        g1p3name = name3
        g1p3elo = elo3
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player4])
        fetch4 = c.fetchone()
        name4 = fetch4[0]
        elo4 = fetch4[1]
        g1p4name = name4
        g1p4elo = elo4
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player5])
        fetch5 = c.fetchone()
        name5 = fetch5[0]
        elo5 = fetch5[1]
        g1p5name = name5
        g1p5elo = elo5
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player6])
        fetch6 = c.fetchone()
        name6 = fetch6[0]
        elo6 = fetch6[1]
        g1p6name = name6
        g1p6elo = elo6
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player7])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g1p7name = name7
        g1p7elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player8])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g1p8name = name8
        g1p8elo = elo8

        if player is None:
                
            if t in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if t in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if t in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        if player is not None:

            if player in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if player in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if player in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        gamestr = f"**Game #{game1id}:** ({game1date})\nTeam 1 {game1team1score}: {g1p1name} [{g1p1elo}], {g1p2name} [{g1p2elo}], {g1p3name} [{g1p3elo}], {g1p4name} [{g1p4elo}]\nTeam 2 {game1team2score}: {g1p5name} [{g1p5elo}], {g1p6name} [{g1p6elo}], {g1p7name} [{g1p7elo}], {g1p8name} [{g1p8elo}]\n"

        game2 = rows[1]
        game2id = game2[0]
        game2player1 = game2[1]
        game2player2 = game2[2]
        game2player3 = game2[3]
        game2player4 = game2[4]
        game2player5 = game2[5]
        game2player6 = game2[6]
        game2player7 = game2[7]
        game2player8 = game2[8]
        game2team1score = game2[9]
        game2team2score = game2[10]
        game2date = game2[13]

        game_2_team_1 = []
        game_2_team_2 = []

        game_2_team_1.append(game2player1)
        game_2_team_1.append(game2player2)
        game_2_team_1.append(game2player3)
        game_2_team_1.append(game2player4)

        game_2_team_2.append(game2player5)
        game_2_team_2.append(game2player6)
        game_2_team_2.append(game2player7)
        game_2_team_2.append(game2player8)
        
        if player is None:
                
            if t in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if t in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if t in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        if player is not None:

            if player in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if player in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if player in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player1])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g2p1name = name7
        g2p1elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player2])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g2p2name = name8
        g2p2elo = elo8
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player3])
        fetch9 = c.fetchone()
        name9 = fetch9[0]
        elo9 = fetch9[1]
        g2p3name = name9
        g2p3elo = elo9
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player4])
        fetch10 = c.fetchone()
        name10 = fetch10[0]
        elo10 = fetch10[1]
        g2p4name = name10
        g2p4elo = elo10
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player5])
        fetch11 = c.fetchone()
        name11 = fetch11[0]
        elo11 = fetch11[1]
        g2p5name = name11
        g2p5elo = elo11
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player6])
        fetch12 = c.fetchone()
        name12 = fetch12[0]
        elo12 = fetch12[1]
        g2p6name = name12
        g2p6elo = elo12
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player7])
        fetch13 = c.fetchone()
        name13 = fetch13[0]
        elo13 = fetch13[1]
        g2p7name = name13
        g2p7elo = elo13
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player8])
        fetch14 = c.fetchone()
        name14 = fetch14[0]
        elo14 = fetch14[1]
        g2p8name = name14
        g2p8elo = elo14

        gamestr += f"**Game #{game2id}:** ({game2date})\nTeam 1 {game2team1score}: {g2p1name} [{g2p1elo}], {g2p2name} [{g2p2elo}], {g2p3name} [{g2p3elo}], {g2p4name} [{g2p4elo}]\nTeam 2 {game2team2score}: {g2p5name} [{g2p5elo}], {g2p6name} [{g2p6elo}], {g2p7name} [{g2p7elo}], {g2p8name} [{g2p8elo}]\n"

        game3 = rows[2]
        game3id = game3[0]
        game3player1 = game3[1]
        game3player2 = game3[2]
        game3player3 = game3[3]
        game3player4 = game3[4]
        game3player5 = game3[5]
        game3player6 = game3[6]
        game3player7 = game3[7]
        game3player8 = game3[8]
        game3team1score = game3[9]
        game3team2score = game3[10]
        game3date = game3[13]

        game_3_team_1 = []
        game_3_team_2 = []

        game_3_team_1.append(game3player1)
        game_3_team_1.append(game3player2)
        game_3_team_1.append(game3player3)
        game_3_team_1.append(game3player4)

        game_3_team_2.append(game3player5)
        game_3_team_2.append(game3player6)
        game_3_team_2.append(game3player7)
        game_3_team_2.append(game3player8)

        if player is None:
                
            if t in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if t in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if t in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if t in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        if player is not None:
                
            if player in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if player in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if player in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if player in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player1])
        fetch15 = c.fetchone()
        name15 = fetch15[0]
        elo15 = fetch15[1]
        g3p1name = name15
        g3p1elo = elo15
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player2])
        fetch16 = c.fetchone()
        name16 = fetch16[0]
        elo16 = fetch16[1]
        g3p2name = name16
        g3p2elo = elo16
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player3])
        fetch17 = c.fetchone()
        name17 = fetch17[0]
        elo17 = fetch17[1]
        g3p3name = name17
        g3p3elo = elo17
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player4])
        fetch18 = c.fetchone()
        name18 = fetch18[0]
        elo18 = fetch18[1]
        g3p4name = name18
        g3p4elo = elo18
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player5])
        fetch19 = c.fetchone()
        name19 = fetch19[0]
        elo19 = fetch19[1]
        g3p5name = name19
        g3p5elo = elo19
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player6])
        fetch20 = c.fetchone()
        name20 = fetch20[0]
        elo20 = fetch20[1]
        g3p6name = name20
        g3p6elo = elo20
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player7])
        fetch21 = c.fetchone()
        name21 = fetch21[0]
        elo21 = fetch21[1]
        g3p7name = name21
        g3p7elo = elo21
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player8])
        fetch22 = c.fetchone()
        name22 = fetch22[0]
        elo22 = fetch22[1]
        g3p8name = name22
        g3p8elo = elo22

        gamestr += f"**Game #{game3id}:** ({game3date})\nTeam 1 {game3team1score}: {g3p1name} [{g3p1elo}], {g3p2name} [{g3p2elo}], {g3p3name} [{g3p3elo}], {g3p4name} [{g3p4elo}]\nTeam 2 {game3team2score}: {g3p5name} [{g3p5elo}], {g3p6name} [{g3p6elo}], {g3p7name} [{g3p7elo}], {g3p8name} [{g3p8elo}]\n"

        game4 = rows[3]
        game4id = game4[0]
        game4player1 = game4[1]
        game4player2 = game4[2]
        game4player3 = game4[3]
        game4player4 = game4[4]
        game4player5 = game4[5]
        game4player6 = game4[6]
        game4player7 = game4[7]
        game4player8 = game4[8]
        game4team1score = game4[9]
        game4team2score = game4[10]
        game4date = game4[13]

        game_4_team_1 = []
        game_4_team_2 = []

        game_4_team_1.append(game4player1)
        game_4_team_1.append(game4player2)
        game_4_team_1.append(game4player3)
        game_4_team_1.append(game4player4)

        game_4_team_2.append(game4player5)
        game_4_team_2.append(game4player6)
        game_4_team_2.append(game4player7)
        game_4_team_2.append(game4player8)

        if player is None:

            if t in game_4_team_1 and game4team2score > game4team1score:

                    game4team2score = "(winner)"
                    game4team1score = "**(loser)**"

            if t in game_4_team_1 and game4team1score > game4team2score:
                
                    game4team1score = "**(winner)**"
                    game4team2score = "(loser)"

            if t in game_4_team_2 and game4team2score > game4team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if t in game_4_team_2 and game4team1score > game4team2score:
                
                    game4team1score = "(winner)"
                    game4team2score = "**(loser)**"


        if player is not None:

            if player in game_4_team_1 and game4team2score > game4team1score:

                    game4team2score = "(winner)"
                    game4team1score = "**(loser)**"

            if player in game_4_team_1 and game4team1score > game4team2score:
                
                    game4team1score = "**(winner)**"
                    game4team2score = "(loser)"

            if player in game_4_team_2 and game4team2score > game4team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if player in game_4_team_2 and game4team1score > game4team2score:
                
                    game4team1score = "(winner)"
                    game4team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player1])
        fetch23 = c.fetchone()
        name23 = fetch23[0]
        elo23 = fetch23[1]
        g4p1name = name23
        g4p1elo = elo23
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player2])
        fetch24 = c.fetchone()
        name24 = fetch24[0]
        elo24 = fetch24[1]
        g4p2name = name24
        g4p2elo = elo24
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player3])
        fetch25 = c.fetchone()
        name25 = fetch25[0]
        elo25 = fetch25[1]
        g4p3name = name25
        g4p3elo = elo25
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player4])
        fetch26 = c.fetchone()
        name26 = fetch26[0]
        elo26 = fetch26[1]
        g4p4name = name26
        g4p4elo = elo26
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player5])
        fetch27 = c.fetchone()
        name27 = fetch27[0]
        elo27 = fetch27[1]
        g4p5name = name27
        g4p5elo = elo27
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player6])
        fetch28 = c.fetchone()
        name28 = fetch28[0]
        elo28 = fetch28[1]
        g4p6name = name28
        g4p6elo = elo28
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player7])
        fetch29 = c.fetchone()
        name29 = fetch29[0]
        elo29 = fetch29[1]
        g4p7name = name29
        g4p7elo = elo29
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game4player8])
        fetch30 = c.fetchone()
        name30 = fetch30[0]
        elo30 = fetch30[1]
        g4p8name = name30
        g4p8elo = elo30

        gamestr += f"**Game #{game4id}:** ({game4date})\nTeam 1 {game4team1score}: {g4p1name} [{g4p1elo}], {g4p2name} [{g4p2elo}], {g4p3name} [{g4p3elo}], {g4p4name} [{g4p4elo}]\nTeam 2 {game4team2score}: {g4p5name} [{g4p5elo}], {g4p6name} [{g4p6elo}], {g4p7name} [{g4p7elo}], {g4p8name} [{g4p8elo}]\n"        

        await ctx.send(gamestr)

        conn.close()

    if len(rows) == 3:

        gamestr = []
        
        game1 = rows[0]
        game1id = game1[0]
        game1player1 = game1[1]
        game1player2 = game1[2]
        game1player3 = game1[3]
        game1player4 = game1[4]
        game1player5 = game1[5]
        game1player6 = game1[6]
        game1player7 = game1[7]
        game1player8 = game1[8]
        game1team1score = game1[9]
        game1team2score = game1[10]
        game1date = game1[13]

        game_1_team_1 = []
        game_1_team_2 = []

        game_1_team_1.append(game1player1)
        game_1_team_1.append(game1player2)
        game_1_team_1.append(game1player3)
        game_1_team_1.append(game1player4)

        game_1_team_2.append(game1player5)
        game_1_team_2.append(game1player6)
        game_1_team_2.append(game1player7)
        game_1_team_2.append(game1player8)

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player1])
        fetch1 = c.fetchone()
        name1 = fetch1[0]
        elo1 = fetch1[1]
        g1p1name = name1
        g1p1elo = elo1
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player2])
        fetch2 = c.fetchone()
        name2 = fetch2[0]
        elo2 = fetch2[1]
        g1p2name = name2
        g1p2elo = elo2
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player3])
        fetch3 = c.fetchone()
        name3 = fetch3[0]
        elo3 = fetch3[1]
        g1p3name = name3
        g1p3elo = elo3
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player4])
        fetch4 = c.fetchone()
        name4 = fetch4[0]
        elo4 = fetch4[1]
        g1p4name = name4
        g1p4elo = elo4
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player5])
        fetch5 = c.fetchone()
        name5 = fetch5[0]
        elo5 = fetch5[1]
        g1p5name = name5
        g1p5elo = elo5
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player6])
        fetch6 = c.fetchone()
        name6 = fetch6[0]
        elo6 = fetch6[1]
        g1p6name = name6
        g1p6elo = elo6
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player7])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g1p7name = name7
        g1p7elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player8])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g1p8name = name8
        g1p8elo = elo8

        if player is None:

            if t in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if t in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if t in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        if player is not None:

            if player in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if player in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if player in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        gamestr = f"**Game #{game1id}:** ({game1date})\nTeam 1 {game1team1score}: {g1p1name} [{g1p1elo}], {g1p2name} [{g1p2elo}], {g1p3name} [{g1p3elo}], {g1p4name} [{g1p4elo}]\nTeam 2 {game1team2score}: {g1p5name} [{g1p5elo}], {g1p6name} [{g1p6elo}], {g1p7name} [{g1p7elo}], {g1p8name} [{g1p8elo}]\n"

        game2 = rows[1]
        game2id = game2[0]
        game2player1 = game2[1]
        game2player2 = game2[2]
        game2player3 = game2[3]
        game2player4 = game2[4]
        game2player5 = game2[5]
        game2player6 = game2[6]
        game2player7 = game2[7]
        game2player8 = game2[8]
        game2team1score = game2[9]
        game2team2score = game2[10]
        game2date = game2[13]

        game_2_team_1 = []
        game_2_team_2 = []

        game_2_team_1.append(game2player1)
        game_2_team_1.append(game2player2)
        game_2_team_1.append(game2player3)
        game_2_team_1.append(game2player4)

        game_2_team_2.append(game2player5)
        game_2_team_2.append(game2player6)
        game_2_team_2.append(game2player7)
        game_2_team_2.append(game2player8)

        if player is None:

            if t in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if t in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if t in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        if player is not None:

            if player in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if player in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if player in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player1])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g2p1name = name7
        g2p1elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player2])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g2p2name = name8
        g2p2elo = elo8
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player3])
        fetch9 = c.fetchone()
        name9 = fetch9[0]
        elo9 = fetch9[1]
        g2p3name = name9
        g2p3elo = elo9
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player4])
        fetch10 = c.fetchone()
        name10 = fetch10[0]
        elo10 = fetch10[1]
        g2p4name = name10
        g2p4elo = elo10
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player5])
        fetch11 = c.fetchone()
        name11 = fetch11[0]
        elo11 = fetch11[1]
        g2p5name = name11
        g2p5elo = elo11
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player6])
        fetch12 = c.fetchone()
        name12 = fetch12[0]
        elo12 = fetch12[1]
        g2p6name = name12
        g2p6elo = elo12
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player7])
        fetch13 = c.fetchone()
        name13 = fetch13[0]
        elo13 = fetch13[1]
        g2p7name = name13
        g2p7elo = elo13
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player8])
        fetch14 = c.fetchone()
        name14 = fetch14[0]
        elo14 = fetch14[1]
        g2p8name = name14
        g2p8elo = elo14

        gamestr += f"**Game #{game2id}:** ({game2date})\nTeam 1 {game2team1score}: {g2p1name} [{g2p1elo}], {g2p2name} [{g2p2elo}], {g2p3name} [{g2p3elo}], {g2p4name} [{g2p4elo}]\nTeam 2 {game2team2score}: {g2p5name} [{g2p5elo}], {g2p6name} [{g2p6elo}], {g2p7name} [{g2p7elo}], {g2p8name} [{g2p8elo}]\n"

        game3 = rows[2]
        game3id = game3[0]
        game3player1 = game3[1]
        game3player2 = game3[2]
        game3player3 = game3[3]
        game3player4 = game3[4]
        game3player5 = game3[5]
        game3player6 = game3[6]
        game3player7 = game3[7]
        game3player8 = game3[8]
        game3team1score = game3[9]
        game3team2score = game3[10]
        game3date = game3[13]

        game_3_team_1 = []
        game_3_team_2 = []

        game_3_team_1.append(game3player1)
        game_3_team_1.append(game3player2)
        game_3_team_1.append(game3player3)
        game_3_team_1.append(game3player4)

        game_3_team_2.append(game3player5)
        game_3_team_2.append(game3player6)
        game_3_team_2.append(game3player7)
        game_3_team_2.append(game3player8)

        if player is None:

            if t in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if t in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if t in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if t in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        if player is not None:

            if player in game_3_team_1 and game3team2score > game3team1score:

                    game3team2score = "(winner)"
                    game3team1score = "**(loser)**"

            if player in game_3_team_1 and game3team1score > game3team2score:
                
                    game3team1score = "**(winner)**"
                    game3team2score = "(loser)"

            if player in game_3_team_2 and game3team2score > game3team1score:

                    game3team2score = "**(winner)**"
                    game3team1score = "(loser)"

            if player in game_3_team_2 and game3team1score > game3team2score:
                
                    game3team1score = "(winner)"
                    game3team2score = "**(loser)**"

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player1])
        fetch15 = c.fetchone()
        name15 = fetch15[0]
        elo15 = fetch15[1]
        g3p1name = name15
        g3p1elo = elo15
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player2])
        fetch16 = c.fetchone()
        name16 = fetch16[0]
        elo16 = fetch16[1]
        g3p2name = name16
        g3p2elo = elo16
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player3])
        fetch17 = c.fetchone()
        name17 = fetch17[0]
        elo17 = fetch17[1]
        g3p3name = name17
        g3p3elo = elo17
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player4])
        fetch18 = c.fetchone()
        name18 = fetch18[0]
        elo18 = fetch18[1]
        g3p4name = name18
        g3p4elo = elo18
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player5])
        fetch19 = c.fetchone()
        name19 = fetch19[0]
        elo19 = fetch19[1]
        g3p5name = name19
        g3p5elo = elo19
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player6])
        fetch20 = c.fetchone()
        name20 = fetch20[0]
        elo20 = fetch20[1]
        g3p6name = name20
        g3p6elo = elo20
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player7])
        fetch21 = c.fetchone()
        name21 = fetch21[0]
        elo21 = fetch21[1]
        g3p7name = name21
        g3p7elo = elo21
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game3player8])
        fetch22 = c.fetchone()
        name22 = fetch22[0]
        elo22 = fetch22[1]
        g3p8name = name22
        g3p8elo = elo22

        gamestr += f"**Game #{game3id}:** ({game3date})\nTeam 1 {game3team1score}: {g3p1name} [{g3p1elo}], {g3p2name} [{g3p2elo}], {g3p3name} [{g3p3elo}], {g3p4name} [{g3p4elo}]\nTeam 2 {game3team2score}: {g3p5name} [{g3p5elo}], {g3p6name} [{g3p6elo}], {g3p7name} [{g3p7elo}], {g3p8name} [{g3p8elo}]\n"

        await ctx.send(gamestr)

        conn.close()

    if len(rows) == 2:

        gamestr = []
        
        game1 = rows[0]
        game1id = game1[0]
        game1player1 = game1[1]
        game1player2 = game1[2]
        game1player3 = game1[3]
        game1player4 = game1[4]
        game1player5 = game1[5]
        game1player6 = game1[6]
        game1player7 = game1[7]
        game1player8 = game1[8]
        game1team1score = game1[9]
        game1team2score = game1[10]
        game1date = game1[13]

        game_1_team_1 = []
        game_1_team_2 = []

        game_1_team_1.append(game1player1)
        game_1_team_1.append(game1player2)
        game_1_team_1.append(game1player3)
        game_1_team_1.append(game1player4)

        game_1_team_2.append(game1player5)
        game_1_team_2.append(game1player6)
        game_1_team_2.append(game1player7)
        game_1_team_2.append(game1player8)

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player1])
        fetch1 = c.fetchone()
        name1 = fetch1[0]
        elo1 = fetch1[1]
        g1p1name = name1
        g1p1elo = elo1
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player2])
        fetch2 = c.fetchone()
        name2 = fetch2[0]
        elo2 = fetch2[1]
        g1p2name = name2
        g1p2elo = elo2
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player3])
        fetch3 = c.fetchone()
        name3 = fetch3[0]
        elo3 = fetch3[1]
        g1p3name = name3
        g1p3elo = elo3
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player4])
        fetch4 = c.fetchone()
        name4 = fetch4[0]
        elo4 = fetch4[1]
        g1p4name = name4
        g1p4elo = elo4
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player5])
        fetch5 = c.fetchone()
        name5 = fetch5[0]
        elo5 = fetch5[1]
        g1p5name = name5
        g1p5elo = elo5
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player6])
        fetch6 = c.fetchone()
        name6 = fetch6[0]
        elo6 = fetch6[1]
        g1p6name = name6
        g1p6elo = elo6
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player7])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g1p7name = name7
        g1p7elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player8])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g1p8name = name8
        g1p8elo = elo8

        if player is None:

            if t in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if t in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if t in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        if player is not None:

            if player in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if player in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if player in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        gamestr = f"**Game #{game1id}:** ({game1date})\nTeam 1 {game1team1score}: {g1p1name} [{g1p1elo}], {g1p2name} [{g1p2elo}], {g1p3name} [{g1p3elo}], {g1p4name} [{g1p4elo}]\nTeam 2 {game1team2score}: {g1p5name} [{g1p5elo}], {g1p6name} [{g1p6elo}], {g1p7name} [{g1p7elo}], {g1p8name} [{g1p8elo}]\n"

        game2 = rows[1]
        game2id = game2[0]
        game2player1 = game2[1]
        game2player2 = game2[2]
        game2player3 = game2[3]
        game2player4 = game2[4]
        game2player5 = game2[5]
        game2player6 = game2[6]
        game2player7 = game2[7]
        game2player8 = game2[8]
        game2team1score = game2[9]
        game2team2score = game2[10]
        game2date = game2[13]

        game_2_team_1 = []
        game_2_team_2 = []

        game_2_team_1.append(game2player1)
        game_2_team_1.append(game2player2)
        game_2_team_1.append(game2player3)
        game_2_team_1.append(game2player4)

        game_2_team_2.append(game2player5)
        game_2_team_2.append(game2player6)
        game_2_team_2.append(game2player7)
        game_2_team_2.append(game2player8)

        if player is None:

            if t in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if t in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if t in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"

        if player is not None:

            if player in game_2_team_1 and game2team2score > game2team1score:

                    game2team2score = "(winner)"
                    game2team1score = "**(loser)**"

            if player in game_2_team_1 and game2team1score > game2team2score:
                
                    game2team1score = "**(winner)**"
                    game2team2score = "(loser)"

            if player in game_2_team_2 and game2team2score > game2team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_2_team_2 and game2team1score > game2team2score:
                
                    game2team1score = "(winner)"
                    game2team2score = "**(loser)**"


        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player1])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g2p1name = name7
        g2p1elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player2])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g2p2name = name8
        g2p2elo = elo8
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player3])
        fetch9 = c.fetchone()
        name9 = fetch9[0]
        elo9 = fetch9[1]
        g2p3name = name9
        g2p3elo = elo9
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player4])
        fetch10 = c.fetchone()
        name10 = fetch10[0]
        elo10 = fetch10[1]
        g2p4name = name10
        g2p4elo = elo10
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player5])
        fetch11 = c.fetchone()
        name11 = fetch11[0]
        elo11 = fetch11[1]
        g2p5name = name11
        g2p5elo = elo11
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player6])
        fetch12 = c.fetchone()
        name12 = fetch12[0]
        elo12 = fetch12[1]
        g2p6name = name12
        g2p6elo = elo12
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player7])
        fetch13 = c.fetchone()
        name13 = fetch13[0]
        elo13 = fetch13[1]
        g2p7name = name13
        g2p7elo = elo13
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game2player8])
        fetch14 = c.fetchone()
        name14 = fetch14[0]
        elo14 = fetch14[1]
        g2p8name = name14
        g2p8elo = elo14

        gamestr += f"**Game #{game2id}:** ({game2date}o)\nTeam 1 {game2team1score}: {g2p1name} [{g2p1elo}], {g2p2name} [{g2p2elo}], {g2p3name} [{g2p3elo}], {g2p4name} [{g2p4elo}]\nTeam 2 {game2team2score}: {g2p5name} [{g2p5elo}], {g2p6name} [{g2p6elo}], {g2p7name} [{g2p7elo}], {g2p8name} [{g2p8elo}]\n"

        await ctx.send(gamestr)

        conn.close()

    if len(rows) == 1:

        gamestr = []
        
        game1 = rows[0]
        game1id = game1[0]
        game1player1 = game1[1]
        game1player2 = game1[2]
        game1player3 = game1[3]
        game1player4 = game1[4]
        game1player5 = game1[5]
        game1player6 = game1[6]
        game1player7 = game1[7]
        game1player8 = game1[8]
        game1team1score = game1[9]
        game1team2score = game1[10]
        game1date = game1[13]

        game_1_team_1 = []
        game_1_team_2 = []

        game_1_team_1.append(game1player1)
        game_1_team_1.append(game1player2)
        game_1_team_1.append(game1player3)
        game_1_team_1.append(game1player4)

        game_1_team_2.append(game1player5)
        game_1_team_2.append(game1player6)
        game_1_team_2.append(game1player7)
        game_1_team_2.append(game1player8)

        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player1])
        fetch1 = c.fetchone()
        name1 = fetch1[0]
        elo1 = fetch1[1]
        g1p1name = name1
        g1p1elo = elo1
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player2])
        fetch2 = c.fetchone()
        name2 = fetch2[0]
        elo2 = fetch2[1]
        g1p2name = name2
        g1p2elo = elo2
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player3])
        fetch3 = c.fetchone()
        name3 = fetch3[0]
        elo3 = fetch3[1]
        g1p3name = name3
        g1p3elo = elo3
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player4])
        fetch4 = c.fetchone()
        name4 = fetch4[0]
        elo4 = fetch4[1]
        g1p4name = name4
        g1p4elo = elo4
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player5])
        fetch5 = c.fetchone()
        name5 = fetch5[0]
        elo5 = fetch5[1]
        g1p5name = name5
        g1p5elo = elo5
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player6])
        fetch6 = c.fetchone()
        name6 = fetch6[0]
        elo6 = fetch6[1]
        g1p6name = name6
        g1p6elo = elo6
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player7])
        fetch7 = c.fetchone()
        name7 = fetch7[0]
        elo7 = fetch7[1]
        g1p7name = name7
        g1p7elo = elo7
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [game1player8])
        fetch8 = c.fetchone()
        name8 = fetch8[0]
        elo8 = fetch8[1]
        g1p8name = name8
        g1p8elo = elo8

        if player is None:

            if t in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if t in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if t in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if t in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        if player is not None:

            if player in game_1_team_1 and game1team2score > game1team1score:

                    game1team2score = "(winner)"
                    game1team1score = "**(loser)**"

            if player in game_1_team_1 and game1team1score > game1team2score:
                
                    game1team1score = "**(winner)**"
                    game1team2score = "(loser)"

            if player in game_1_team_2 and game1team2score > game1team1score:

                    game1team2score = "**(winner)**"
                    game1team1score = "(loser)"

            if player in game_1_team_2 and game1team1score > game1team2score:
                
                    game1team1score = "(winner)"
                    game1team2score = "**(loser)**"

        gamestr = f"**Game #{game1id}:** ({game1date})\nTeam 1 {game1team1score}: {g1p1name} [{g1p1elo}], {g1p2name} [{g1p2elo}], {g1p3name} [{g1p3elo}], {g1p4name} [{g1p4elo}]\nTeam 2 {game1team2score}: {g1p5name} [{g1p5elo}], {g1p6name} [{g1p6elo}], {g1p7name} [{g1p7elo}], {g1p8name} [{g1p8elo}]\n"

        await ctx.send(gamestr)  

        conn.close()     

    if len(rows) == 0:

        if player is None:

            await ctx.send(f"You have no recent games.")

        if player is not None:
            
            c.execute("SELECT name FROM players WHERE ID = ?", [player])
            name = c.fetchone()[0]
            await ctx.send(f"There are no recent games for **{name}**.")
            
        conn.close()

@client.command()
@commands.has_any_role('League Admin', 'Primary Developer')
async def forcejoin(ctx, player):
    '''Forcejoins a user into the lobby.'''

    global PLAYERS, PLAYERS2, PLAYERS3, GAME, GAME2, GAME3, RUNNING, RUNNING2, RUNNING3, db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        t = ctx.message.author.id
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players WHERE ID = ?", [player])
        user = c.fetchone()
        name = user[0]

        if GAME:
            PLAYERS = list(set(PLAYERS))
            PLAYERS.append(player)
            joined_dic[player] = gettime()

            await ctx.channel.send(f"**{name}** was forced into the lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        t = ctx.message.author.id
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players_team WHERE ID = ?", [player])
        user = c.fetchone()
        name = user[0]

        if GAME2:
            PLAYERS2 = list(set(PLAYERS2))
            PLAYERS2.append(player)
            joined_dic[player] = gettime()

            await ctx.channel.send(f"**{name}** was forced into the lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:

        t = ctx.message.author.id
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players_team WHERE ID = ?", [player])
        user = c.fetchone()
        name = user[0]

        if GAME3:
            PLAYERS3 = list(set(PLAYERS3))
            PLAYERS3.append(player)
            joined_dic[player] = gettime()

            await ctx.channel.send(f"**{name}** was forced into the lobby.")

        conn.commit()
        conn.close()


@client.command(aliases=["h"])
@commands.cooldown(1, 5, commands.BucketType.user)
async def here(ctx):
    '''Resets the lobby timer for inactivity kick.'''

    global PLAYERS, joined_dic, repeat_list

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

        t = ctx.message.author.id

        try:

            repeat_list.remove(t)
            joined_dic[t] = gettime()
            await ctx.send("All good.")

        except:

            joined_dic[t] = gettime()
            await ctx.send("All good.")

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def peak(ctx, name=None):
    
    '''Show's the highest ELO reached by a player.'''

    global joined_dic

    if ctx.channel.id == ones_channel.id:

        if name == None:
            x = ctx.author.id
            joined_dic[x] = gettime()
            t = ctx.message.author.id
            conn = sqlite3.connect(db_path, uri=True)
            c = conn.cursor()
            #player = find_userid_by_name(ctx, name)
            if x is None:
                await ctx.channel.send("No user found by that name.")
                return
            c.execute("SELECT name, record FROM players WHERE ID = ?", [x])
            user = c.fetchone()
            name = user[0]
            record = user[1]

            await ctx.channel.send(f"**{name}** has an elo peak of **{record}**.")

        elif name:

            x = ctx.author.id
            joined_dic[x] = gettime()
            t = ctx.message.author.id
            conn = sqlite3.connect(db_path, uri=True)
            c = conn.cursor()
            player = find_userid_by_name(ctx, name)
            if player is None:
                await ctx.channel.send("No user found by that name.")
                return
            c.execute("SELECT name, record FROM players WHERE ID = ?", [player])
            user = c.fetchone()
            name = user[0]
            record = user[1]

            await ctx.channel.send(f"**{name}** has an elo peak of **{record}**.")

    if ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:

        if name == None:
            x = ctx.author.id
            joined_dic[x] = gettime()
            t = ctx.message.author.id
            conn = sqlite3.connect(db_path, uri=True)
            c = conn.cursor()
            #player = find_userid_by_name(ctx, name)
            if x is None:
                await ctx.channel.send("No user found by that name.")
                return
            c.execute("SELECT name, record FROM players_team WHERE ID = ?", [x])
            user = c.fetchone()
            name = user[0]
            record = user[1]

            await ctx.channel.send(f"**{name}** has an elo peak of **{record}**.")

        elif name:

            x = ctx.author.id
            joined_dic[x] = gettime()
            t = ctx.message.author.id
            conn = sqlite3.connect(db_path, uri=True)
            c = conn.cursor()
            player = find_userid_by_name(ctx, name)
            if player is None:
                await ctx.channel.send("No user found by that name.")
                return
            c.execute("SELECT name, record FROM players_team WHERE ID = ?", [player])
            user = c.fetchone()
            name = user[0]
            record = user[1]

            await ctx.channel.send(f"**{name}** has an elo peak of **{record}**.")


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def kick(ctx, player):

    """Kicks a player out of the lobby."""

    global PLAYERS, GAME, db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        n = ctx.author.name
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players WHERE ID = ?", [player])
        fetch = c.fetchone()
        user = fetch[0]

        try:
            if GAME:
                PLAYERS = list(set(PLAYERS))

                PLAYERS.remove(player)

                await ctx.channel.send("**" + str(user) + "** has been kicked from the lobby by **" + str(n) + "**.")
        except ValueError:
            await ctx.channel.send("**" + str(user) + " is not in lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        n = ctx.author.name
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players_team WHERE ID = ?", [player])
        fetch = c.fetchone()
        user = fetch[0]

        try:
            if GAME2:
                PLAYERS2 = list(set(PLAYERS2))

                PLAYERS2.remove(player)

                await ctx.channel.send("**" + str(user) + "** has been kicked from the lobby by **" + str(n) + "**.")
        except ValueError:
            await ctx.channel.send("**" + str(user) + " is not in lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        n = ctx.author.name
        player = find_userid_by_name(ctx, player)
        if player is None:
            await ctx.channel.send("No user found by that name.")
            return
        c.execute("SELECT name FROM players_team WHERE ID = ?", [player])
        fetch = c.fetchone()
        user = fetch[0]

        try:
            if GAME3:
                PLAYERS3 = list(set(PLAYERS3))

                PLAYERS3.remove(player)

                await ctx.channel.send("**" + str(user) + "** has been kicked from the lobby by **" + str(n) + "**.")
        except ValueError:
            await ctx.channel.send("**" + str(user) + " is not in lobby.")

        conn.commit()
        conn.close()

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def games(ctx):
    '''Shows current games being played.'''

    global PLAYERS, GAME, db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        conn = sqlite3.connect(db_path, uri=True)
        t = ctx.message.author.id
        c = conn.cursor()
        
        c.execute("SELECT ID FROM games WHERE s1 IS NULL")
        games = c.fetchall()
        
        if len(games) == 0:
            await ctx.channel.send("There are no games running.")
        else:
            if len(games) == 1:
                #await ctx.channel.send("Found " + str(len(games)) + " active game!")
                pass
                
            else:
                print("Found " + str(len(games)) + " active games!")

            count = 1
            for game in games:
                c.execute("SELECT p1, p2 FROM games WHERE ID is ?", game)
                players = c.fetchone()

                c.execute("SELECT elo FROM PLAYERS where ID = ?", [players[0]])
                p1 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS where ID = ?", [players[1]])
                p2 = c.fetchone()[0]

                team1 = int(round(p1))
                team2 = int(round(p2))
                
                gameStr = "**Game " + str(game[0]) + ": **\n**Team 1: (" + str(team1) + ")** "
                count += 1
                playerCnt = 1
                for player in players:
                    c.execute("SELECT name, elo FROM players where ID = ?", [player])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(result[1]))
                    gameStr += name + " [" + str(pts) + "]  "
                    if playerCnt == 1:
                        gameStr += "\n**Team 2: (" + str(team2) + ")** "
                    playerCnt += 1
                c.execute("SELECT currentg from players where currentg > 0")
                gn = c.fetchone()
                gID = gn[0]
                c.execute("SELECT ID, start_time FROM games WHERE ID = ?", [str(gID)])
                time = c.fetchone()
                start_time = time[1]
                done = datetime.datetime.now()
                done1 = done.strftime("%M")
                uptime = int(done1) - start_time
                await ctx.channel.send(gameStr)
                if uptime is 0:
                    await ctx.channel.send("Uptime: a few seconds.")
                if uptime is 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minute.")
                if uptime > 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minutes.")
                if uptime < 0:
                    calc = int(uptime) + 60
                    await ctx.channel.send("Uptime: " + str(calc) + " minutes.")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        conn = sqlite3.connect(db_path, uri=True)
        t = ctx.message.author.id
        c = conn.cursor()
        
        c.execute("SELECT ID FROM games_team WHERE s1 IS NULL")
        games = c.fetchall()
        
        if len(games) == 0:
            await ctx.channel.send("There are no games running.")
        else:
            if len(games) == 1:

                pass
                
            else:

                print("Found " + str(len(games)) + " active games!")

            count = 1
            for game in games:
                c.execute("SELECT p1, p2, p3, p4 FROM games_team WHERE ID is ?", game)
                players = c.fetchone()

                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[0]])
                p1 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[1]])
                p2 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[2]])
                p3 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[3]])
                p4 = c.fetchone()[0]

                team1 = p1+p2
                team2 = p3+p4
                
                gameStr = "**Game " + str(game[0]) + ": **\n**Team 1: (" + str(team1) + ")** "
                count += 1
                playerCnt = 1
                for player in players:
                    c.execute("SELECT name, elo FROM players_team where ID = ?", [player])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(result[1]))
                    gameStr += name + " [" + str(pts) + "]  "
                    if playerCnt == 2:
                        gameStr += "\n**Team 2: (" + str(team2) + ")** "
                    playerCnt += 1
                c.execute("SELECT currentg from players_team where currentg > 0")
                gn = c.fetchone()
                gID = gn[0]
                c.execute("SELECT ID, start_time FROM games_team WHERE ID = ?", [str(gID)])
                time = c.fetchone()
                start_time = time[1]
                done = datetime.datetime.now()
                done1 = done.strftime("%M")
                uptime = int(done1) - start_time
                await ctx.channel.send(gameStr)
                if uptime is 0:
                    await ctx.channel.send("Uptime: a few seconds.")
                if uptime is 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minute.")
                if uptime > 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minutes.")
                if uptime < 0:
                    calc = int(uptime) + 60
                    await ctx.channel.send("Uptime: " + str(calc) + " minutes.")

        conn.commit()
        conn.close()


    if ctx.channel.id == threes_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        conn = sqlite3.connect(db_path, uri=True)
        t = ctx.message.author.id
        c = conn.cursor()
        
        c.execute("SELECT ID FROM games_team WHERE s1 IS NULL")
        games = c.fetchall()
        
        if len(games) == 0:
            await ctx.channel.send("There are no games running.")
        else:
            if len(games) == 1:

                pass
                
            else:

                print("Found " + str(len(games)) + " active games!")

            count = 1
            for game in games:
                c.execute("SELECT p1, p2, p3, p4, p5, p6 FROM games_team WHERE ID is ?", game)
                players = c.fetchone()

                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[0]])
                p1 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[1]])
                p2 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[2]])
                p3 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[3]])
                p4 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[4]])
                p5 = c.fetchone()[0]
                c.execute("SELECT elo FROM PLAYERS_TEAM where ID = ?", [players[5]])
                p6 = c.fetchone()[0]

                team1 = p1+p2+p3
                team2 = p4+p5+p6
                
                gameStr = "**Game " + str(game[0]) + ": **\n**Team 1: (" + str(team1) + ")** "
                count += 1
                playerCnt = 0
                for player in players:
                    c.execute("SELECT name, elo FROM players_team where ID = ?", [player])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(result[1]))
                    gameStr += name + " [" + str(pts) + "]  "
                    if playerCnt == 2:
                        gameStr += "\n**Team 2: (" + str(team2) + ")** "
                    playerCnt += 1
                c.execute("SELECT currentg from players_team where currentg > 0")
                gn = c.fetchone()
                gID = gn[0]
                c.execute("SELECT ID, start_time FROM games_team WHERE ID = ?", [str(gID)])
                time = c.fetchone()
                start_time = time[1]
                done = datetime.datetime.now()
                done1 = done.strftime("%M")
                uptime = int(done1) - start_time
                await ctx.channel.send(gameStr)
                if uptime is 0:
                    await ctx.channel.send("Uptime: a few seconds.")
                if uptime is 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minute.")
                if uptime > 1:
                    await ctx.channel.send("Uptime: " + str(uptime) + " minutes.")
                if uptime < 0:
                    calc = int(uptime) + 60
                    await ctx.channel.send("Uptime: " + str(calc) + " minutes.")

        conn.commit()
        conn.close()

@client.command()
@commands.has_any_role("Dev")
@commands.has_permissions(manage_messages=True)
async def purge(ctx, limit: int, channel:discord.TextChannel=None):

    """Delete's messages in channels."""

    if channel is None:

        await ctx.channel.purge(limit=limit)

@client.command(aliases=["j"])
async def join(ctx, gametype=None):

    """Joins a player into the lobby."""

    global PLAYERS, PLAYERS2, PLAYERS3, RUNNING, RUNNING2, RUNNING3, GAME, GAME2, GAME3, db_path, TEAMS, TEAMS2, TEAMS3, DRAFTING, CUSTOM_LOCK, LIMIT, STARTING, STARTING2, STARTING3, lobby_channel, draft_channel, BANNED, joined_dic, gametype_lobby, gametype_lobby2, gametype_lobby3, captain_team_one, captain_team_two

    if ctx.channel.id == twos_channel.id:

        print("here")

        x = ctx.author
        t = ctx.message.author.id
        n = ctx.message.author.name
        member = ctx.author
        date = datetime.datetime.now()
        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        c.execute("SELECT elo FROM players_team WHERE ID = ?", [t])
        mon = c.fetchone()

        if mon == None:
            c.execute('INSERT INTO players_team VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                    [t, n, "Empty", date, str(profile)])
            c.execute("INSERT INTO warnings2 VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [t,n])
            await ctx.channel.send("You are now registered.")
            role = discord.utils.get(ctx.guild.roles, name="League")
            await member.add_roles(role)
            conn.commit()

        c.execute("SELECT ID, name, elo, fresh_warns FROM players_team where ID = ?", [t])
        creator = ctx.message.author.name
        results = c.fetchone()
        ids = results[0]
        pts = int(round(results[2]))
        warns = results[3]

        c = conn.cursor()

        c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])

        A = c.fetchone()[0] is None

        if gametype == None:

            gametype_lobby2 = []
            gametype_lobby2.append("normal")

            if t in PLAYERS2:
                await ctx.channel.send("You're already in the lobby.")
                return

            if GAME2 and A:

                if warns > 2:
                    await ctx.send("You are currently banned.")
                    return

                else:

                    PLAYERS2.append(t)
                    c.execute("SELECT ID, name, elo FROM players_team where ID = ?", [t])
                    result = c.fetchone()
                    ids = result[0]
                    name = result[1]
                    pts = int(round(result[2]))
                    joined_dic[t] = gettime()
                    elo_dic[t] = str(pts)
                    await ctx.channel.send(
                        name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS2))) + ")**")

            elif GAME2:
                await ctx.channel.send("You're still in a game.")

            if DRAFTING2:
                await ctx.channel.send("Can't join a drafting lobby.")

            if warns > 2:
                await ctx.channel.send("You are banned.")
                return

            else:
                c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])
                B = c.fetchone()[0]
                if B is None:
                    if not RUNNING2:
                        t = ctx.message.author.id
                        t2 = ctx.author.id
                        conn = sqlite3.connect(db_path)
                        c = conn.cursor()
                        counter = 0
                        SKATER_LIST2 = []
                        RUNNING2 = True
                        GAME2 = True
                        STARTING2 = False
                        PLAYERS2.append(ids)
                        joined_dic[t] = gettime()
                        elo_dic[t] = str(pts)
                        await ctx.channel.send("Created a new lobby.")
                        await ctx.channel.send(
                            f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS2))) + ")**")

                        while len(PLAYERS2) < 4 and counter < 900000000:
                            if STARTING2:
                                STARTING2 = False
                                print("Not enough players.")
                            await asyncio.sleep(10)
                            counter += 1
                            if len(set(PLAYERS2)) > 3:
                                STARTING2 = True
                                counter -= 1
                                #await ctx.channel.send(f"Starting lobby **(normal)** in **30** seconds.")
                                #await asyncio.sleep(30)
                            if len(set(PLAYERS2)) == 0 and counter > 6:
                                GAME2 = False
                                STARTING2 = False
                                RUNNING2 = False
                                return None

                        GAME2 = False
                        STARTING2 = False
                        if len(PLAYERS2) > 3:

                            np.random.shuffle(PLAYERS2)

                            ELOS = []
                            values = []
                            PLAYERS_AND_ELO = []
                            for t in PLAYERS2:
                                c.execute("SELECT elo, name FROM players_team WHERE ID = ?", [str(t)])
                                elo = c.fetchone()[0]
                                ELOS.append((t, int(elo)))
                                values.append(int(elo))

                            for t in PLAYERS2:
                                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [str(t)])
                                fetch = c.fetchone()
                                players_name = fetch[0]
                                players_elo = fetch[1]
                                PLAYERS_AND_ELO.append(players_name)
                                PLAYERS_AND_ELO.append(players_elo)

                            mu = np.mean(values)
                            sigma = 300
                            mask = np.ones(len(PLAYERS2)).astype(bool)

                            counterb = 0

                            while(sum(mask) != 4) and counterb < 250000:
                                for k,x in enumerate(values):
                                    mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
                                counterb += 1

                            if sum(mask) == 4:
                                ELOS = list(np.array(ELOS)[mask])

                                team1 = sum([int(b[1]) for b in ELOS[0:2]])
                                team2 = sum([int(b[1]) for b in ELOS[2:4]])

                                diff = abs(team1-team2)

                                for t in itertools.permutations(ELOS, 4):
                                    team1 = sum([int(b[1]) for b in t[0:2]])
                                    team2 = sum([int(b[1]) for b in t[2:4]])
                                    if abs(team1 - team2) < diff:
                                        ELOS = t
                                        diff = abs(team1-team2)
                                c.execute("SELECT MAX(ID) from games_team")
                                gameID = c.fetchone()[0]
                                if gameID is None:
                                    gameID = 1
                                else:
                                    gameID = int(gameID) + 1

                                playerID = []
                                for t in ELOS:
                                    playerID.append(str(t[0]))

                                c.execute('INSERT INTO games_team VALUES(?, ?, ?, ?, ?, NULL, NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)
                                start = datetime.datetime.now()
                                time = start.strftime("%M")
                                time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")
                                c.execute("UPDATE GAMES_team set start_time = ? WHERE ID = ?", [int(time), str(gameID)])
                                c.execute("UPDATE GAMES_team SET gamedate = ? WHERE ID = ?", [time_data2[0] + " " + time_data2[1] + " " + time_data2[2],str(gameID)])

                                for t in playerID:
                                    c.execute("UPDATE players_team SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

                                capt = 0
                                captid = ""
                                # finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:2]])) + "):** "
                                # for k,t in enumerate(playerID):
                                #     c.execute("SELECT name FROM players WHERE ID = ?", [str(t)])
                                #     print(playerID)
                                #     name = c.fetchone()[0]
                                #     if(capt < int(ELOS[k][1])):
                                #         capt = int(ELOS[k][1])
                                #         captid = name
                                #     finalstr += name + "   "
                                #     if k == 1:
                                #         finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[2:4]])) + "): **"
                                #         capt = 0
                                #         captid = ""

                                notestr = ""
                                for t in playerID:
                                    notestr += "<@" + t + "> "

                                total_elos = team1 + team2
                                team1_percentage = np.floor(team1 / total_elos * 100)
                                t1pp = round(team1_percentage)
                                team2_percentage = np.floor(team2 / total_elos * 100)
                                t2pp = round(team2_percentage)
                                diffe = np.abs(team1 - team2)

                                player_1 = f"{PLAYERS_AND_ELO[0]} [{int(round(PLAYERS_AND_ELO[1]))}]"
                                player_2 = f"{PLAYERS_AND_ELO[2]} [{int(round(PLAYERS_AND_ELO[3]))}]"
                                player_3 = f"{PLAYERS_AND_ELO[4]} [{int(round(PLAYERS_AND_ELO[5]))}]"
                                player_4 = f"{PLAYERS_AND_ELO[6]} [{int(round(PLAYERS_AND_ELO[7]))}]"

                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[0]])
                                p1 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[2]])
                                p2 = c.fetchone()[0]

                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[4]])
                                p3 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[6]])
                                p4 = c.fetchone()[0]

                                game_dict = {}
                                game_dict["ids"] = [p1, p2, p3, p4]
                                game_dict["teams"] = [[p1, p2], [p3, p4]]
                                game_dict["player_to_team"] = {}
                                for i, team in enumerate(game_dict["teams"]):
                                    for player in team:
                                        game_dict["player_to_team"][player] = i
                                game_dict["player_votes"] = defaultdict(str)
                                game_dict["vote_count"] = 0
                                game_dict["won"] = [0, 0, 0]
                                game_dict["lost"] = [0, 0, 0]
                                game_dict["draw"] = [0, 0, 0]
                                global_dict[gameID] = game_dict

                                team_1_sum = PLAYERS_AND_ELO[1]+PLAYERS_AND_ELO[3]
                                team_2_sum = PLAYERS_AND_ELO[5]+PLAYERS_AND_ELO[7]

                                final = f"**Game #{gameID} started:**\n**Team 1 ({int(round(team_1_sum))}):** {player_1} {player_2}\n**Team 2 ({int(round(team_2_sum))}):** {player_3} {player_4}\nTotal ELO Difference: {diff}.\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."

                                # finalstr += "\nTotal ELO Difference: " + str(diff) + "."
                                # finalstr += f"\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
                                guild = discord.utils.get(client.guilds, id=383292703955222542)
                                lobby_channel = discord.utils.get(guild.channels, id=790313583484731422)
                                await lobby_channel.send(f"{final}\n{notestr}")

                                conn.commit()

                                PLAYERS2 = []

                            else:
                                await ctx.channel.send("Could not balance lobby.")
                                PLAYERS2 = []
                        else:
                            await ctx.channel.send("Not Enough Players")
                            PLAYERS2 = []

                        PLAYERS2 = []
                        RUNNING2 = False
                        gametype_lobby2 = []

                        conn.close()

    # if ctx.channel.id == threes_channel.id:

    #     x = ctx.author
    #     t = ctx.message.author.id
    #     n = ctx.message.author.name
    #     member = ctx.author
    #     date = datetime.datetime.now()
    #     profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"
    #     conn = sqlite3.connect(db_path, uri=True)
    #     c = conn.cursor()
    #     c.execute("SELECT elo FROM players_team WHERE ID = ?", [t])
    #     mon = c.fetchone()

    #     if mon == None:
    #         c.execute('INSERT INTO players_team VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
    #                 [t, n, "Empty", date, str(profile)])
    #         c.execute("INSERT INTO warnings VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [t,n])
    #         await ctx.channel.send("You are now registered.")
    #         role = discord.utils.get(ctx.guild.roles, name="League")
    #         await member.add_roles(role)
    #         conn.commit()

    #     c.execute("SELECT ID, name, elo, fresh_warns FROM players_team where ID = ?", [t])
    #     creator = ctx.message.author.name
    #     results = c.fetchone()
    #     ids = results[0]
    #     pts = int(round(results[2]))
    #     warns = results[3]

    #     c = conn.cursor()

    #     c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])

    #     A = c.fetchone()[0] is None

    #     if gametype == None:

    #         gametype_lobby3 = []
    #         gametype_lobby3.append("normal")

    #         if t in PLAYERS3:
    #             joined_dic[t] = gettime()
    #             await ctx.channel.send("You're already in the lobby.")
    #             return

    #         if GAME3 and A:

    #             if warns > 2:
    #                 await ctx.send("You are currently banned.")
    #                 return

    #             else:

    #                 PLAYERS3.append(t)
    #                 c.execute("SELECT ID, name, elo FROM players_team where ID = ?", [t])
    #                 result = c.fetchone()
    #                 ids = result[0]
    #                 name = result[1]
    #                 pts = int(round(result[2]))
    #                 joined_dic[t] = gettime()
    #                 elo_dic[t] = str(pts)
    #                 await ctx.channel.send(
    #                     name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS3))) + ")**")

    #         elif GAME3:
    #             await ctx.channel.send("You're still in a game.")

    #         if DRAFTING:
    #             await ctx.channel.send("Can't join a drafting lobby.")

    #         if warns > 2:
    #             await ctx.channel.send("You are banned.")
    #             return

    #         else:
    #             c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])
    #             B = c.fetchone()[0]
    #             if B is None:
    #                 if not RUNNING3:
    #                     t = ctx.message.author.id
    #                     t2 = ctx.author.id
    #                     conn = sqlite3.connect(db_path)
    #                     c = conn.cursor()
    #                     counter = 0
    #                     SKATER_LIST = []
    #                     RUNNING3 = True
    #                     GAME3 = True
    #                     STARTING3 = False
    #                     PLAYERS3.append(ids)
    #                     joined_dic[t] = gettime()
    #                     elo_dic[t] = str(pts)
    #                     await ctx.channel.send("Created a new lobby.")
    #                     await ctx.channel.send(
    #                         f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS3))) + ")**")

    #                     while len(PLAYERS3) < 6 and counter < 900000000:
    #                         # if STARTING:
    #                         #     STARTING = False
    #                         #     print("Not enough players.")
    #                         await asyncio.sleep(10)
    #                         counter += 1
    #                         if len(set(PLAYERS3)) > 5:
    #                             STARTING3 = True
    #                             counter -= 1
    #                             #await ctx.channel.send(f"Starting lobby **({gametype_lobby3[0]})** in **30** seconds.")
    #                             #await asyncio.sleep(0)
    #                         if len(set(PLAYERS3)) == 0 and counter > 6:
    #                             GAME3 = False
    #                             STARTING3 = False
    #                             RUNNING3 = False
    #                             return None

    #                     GAME3 = False
    #                     STARTING3 = False
    #                     if len(PLAYERS3) > 5:

    #                         np.random.shuffle(PLAYERS3)

    #                         ELOS = []
    #                         values = []
    #                         PLAYERS_AND_ELO = []
    #                         for t in PLAYERS3:
    #                             c.execute("SELECT elo, name FROM players_team WHERE ID = ?", [str(t)])
    #                             elo = c.fetchone()[0]
    #                             ELOS.append((t, int(elo)))
    #                             values.append(int(elo))

    #                         mu = np.mean(values)
    #                         sigma = 300
    #                         mask = np.ones(len(PLAYERS3)).astype(bool)

    #                         counterb = 0

    #                         while(sum(mask) != 6) and counterb < 250000:
    #                             for k,x in enumerate(values):
    #                                 mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
    #                             counterb += 1

    #                         if sum(mask) == 6:
    #                             ELOS = list(np.array(ELOS)[mask])

    #                             team1 = sum([int(b[1]) for b in ELOS[0:3]])
    #                             team2 = sum([int(b[1]) for b in ELOS[3:6]])

    #                             diff = abs(team1-team2)

    #                             for t in itertools.permutations(ELOS, 6):
    #                                 team1 = sum([int(b[1]) for b in t[0:3]])
    #                                 team2 = sum([int(b[1]) for b in t[3:6]])
    #                                 if abs(team1 - team2) < diff:
    #                                     ELOS = t
    #                                     diff = abs(team1-team2)
    #                             c.execute("SELECT MAX(ID) from games_team")
    #                             gameID = c.fetchone()[0]
    #                             if gameID is None:
    #                                 gameID = 1
    #                             else:
    #                                 gameID = int(gameID) + 1

    #                             playerID = []
    #                             for t in ELOS:
    #                                 playerID.append(str(t[0]))

    #                             c.execute('INSERT INTO games_team VALUES(?, ?, ?, ?, ?, ?, ?, NULL, NULL, NULL,NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)

    #                             start = datetime.datetime.now()
    #                             time = start.strftime("%M")
    #                             time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")
    #                             c.execute("UPDATE games_team set start_time = ? WHERE ID = ?", [int(time), str(gameID)])
    #                             c.execute("UPDATE games_team SET gamedate = ? WHERE ID = ?", [time_data2[0] + " " + time_data2[1] + " " + time_data2[2],str(gameID)])

    #                             for t in playerID:
    #                                 c.execute("UPDATE players_team SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

    #                             capt = 0
    #                             captid = ""
    #                             finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:3]])) + "):** "
    #                             for k,t in enumerate(playerID):
    #                                 c.execute("SELECT name FROM players_team WHERE ID = ?", [str(t)])
    #                                 name = c.fetchone()[0]
    #                                 if(capt < int(ELOS[k][1])):
    #                                     capt = int(ELOS[k][1])
    #                                     captid = name
    #                                 finalstr += name + "   "
    #                                 if k == 1:
    #                                     finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[3:6]])) + "): **"
    #                                     capt = 0
    #                                     captid = ""

    #                             conn.commit()

    #                             notestr = ""
    #                             for t in playerID:
    #                                 notestr += "<@" + t + "> "

    #                             total_elo = team1 + team2
    #                             team1_percent = team1 / total_elo * 100
    #                             t1p = round(team1_percent)
    #                             team2_percent = team2 / total_elo * 100
    #                             t2p = round(team2_percent)
    #                             diff = np.abs(team1 - team2)

    #                             c.execute("SELECT MAX(ID) FROM games_team")
    #                             gamenum = c.fetchone()[0]

    #                             c.execute("SELECT P1,P2,P3,P4,P5,P6 FROM games_team WHERE ID = ?", [gamenum])
    #                             PLAYER_DISPLAY = c.fetchall()[0]
    #                             print(PLAYER_DISPLAY)

    #                             for t in PLAYER_DISPLAY:
    #                                 c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [str(t)])
    #                                 fetch = c.fetchone()
    #                                 players_name = fetch[0]
    #                                 players_elo = fetch[1]
    #                                 PLAYERS_AND_ELO.append(players_name)
    #                                 PLAYERS_AND_ELO.append(players_elo)

    #                             player_1 = f"{PLAYERS_AND_ELO[0]} [{int(round(PLAYERS_AND_ELO[1]))}]"
    #                             player_2 = f"{PLAYERS_AND_ELO[2]} [{int(round(PLAYERS_AND_ELO[3]))}]"
    #                             player_3 = f"{PLAYERS_AND_ELO[4]} [{int(round(PLAYERS_AND_ELO[5]))}]"
    #                             player_4 = f"{PLAYERS_AND_ELO[6]} [{int(round(PLAYERS_AND_ELO[7]))}]"
    #                             player_5 = f"{PLAYERS_AND_ELO[8]} [{int(round(PLAYERS_AND_ELO[9]))}]"
    #                             player_6 = f"{PLAYERS_AND_ELO[10]} [{int(round(PLAYERS_AND_ELO[11]))}]"

    #                             team_1_sum = PLAYERS_AND_ELO[1] + PLAYERS_AND_ELO[3] + PLAYERS_AND_ELO[5]
    #                             team_2_sum = PLAYERS_AND_ELO[7] + PLAYERS_AND_ELO[9] + PLAYERS_AND_ELO[11]

    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[0]])
    #                             p1 = c.fetchone()[0]
                                
    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[2]])
    #                             p2 = c.fetchone()[0]

    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[4]])
    #                             p3 = c.fetchone()[0]
                                
    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[6]])
    #                             p4 = c.fetchone()[0]

    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[8]])
    #                             p5 = c.fetchone()[0]
                                
    #                             c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [PLAYERS_AND_ELO[10]])
    #                             p6 = c.fetchone()[0]

    #                             game_dict = {}
    #                             game_dict["ids"] = [p1, p2, p3, p4, p5, p6]
    #                             game_dict["teams"] = [[p1, p2, p3], [p4, p5, p6]]
    #                             game_dict["player_to_team"] = {}
    #                             for i, team in enumerate(game_dict["teams"]):
    #                                 for player in team:
    #                                     game_dict["player_to_team"][player] = i
    #                             game_dict["player_votes"] = defaultdict(str)
    #                             game_dict["vote_count"] = 0
    #                             game_dict["won"] = [0, 0, 0]
    #                             game_dict["lost"] = [0, 0, 0]
    #                             game_dict["draw"] = [0, 0, 0]
    #                             global_dict[gameID] = game_dict

    #                             final = f"**Game #{gameID} started:**\n**Team 1 ({int(round(team_1_sum))}):** {player_1}, {player_2}, {player_3}\n**Team 2 ({int(round(team_2_sum))}):** {player_4}, {player_5}, {player_6}\nTotal ELO Difference: {diff}.\nTeam 1: {t1p}% probability to win;Team 2: {t2p}% probability to win."

    #                             # finalstr += "\nTotal ELO Difference: " + str(diff) + "."
    #                             # finalstr += f"\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
    #                             guild = discord.utils.get(client.guilds, id=784960512534380586)
    #                             lobby_channel = discord.utils.get(guild.channels, id=785225698419408907)
    #                             await lobby_channel.send(f"{final}\n{notestr}")

    #                             PLAYERS3 = []

    #                         else:
    #                             await ctx.channel.send("Could not balance lobby.")
    #                             PLAYERS3 = []
    #                     else:
    #                         await ctx.channel.send("Not Enough Players")
    #                         PLAYERS3 = []

    #                     PLAYERS3 = []
    #                     RUNNING3 = False
    #                     gametype_lobby3 = []

    #                     conn.close()

    if ctx.channel.id == threes_channel.id:

        x = ctx.author
        t = ctx.message.author.id
        n = ctx.message.author.name
        member = ctx.author
        date = datetime.datetime.now()
        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        c.execute("SELECT elo FROM players_team WHERE ID = ?", [t])
        mon = c.fetchone()

        if mon == None:
            c.execute('INSERT INTO players_team VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                    [t, n, "Empty", date, str(profile)])
            c.execute("INSERT INTO warnings VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [t,n])
            await ctx.channel.send("You are now registered.")
            role = discord.utils.get(ctx.guild.roles, name="League")
            await member.add_roles(role)
            conn.commit()

        c.execute("SELECT ID, name, elo, fresh_warns FROM players_team where ID = ?", [t])
        creator = ctx.message.author.name
        results = c.fetchone()
        ids = results[0]
        pts = int(round(results[2]))
        warns = results[3]

        c = conn.cursor()

        c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])

        A = c.fetchone()[0] is None

        if gametype == None:

            gametype_lobby3 = []
            gametype_lobby3.append("normal")

            if t in PLAYERS3:
                joined_dic[t] = gettime()
                await ctx.channel.send("You're already in the lobby.")
                return

            if GAME3 and A:

                if warns > 2:
                    await ctx.send("You are currently banned.")
                    return

                else:

                    PLAYERS3.append(t)
                    c.execute("SELECT ID, name, elo FROM players_team where ID = ?", [t])
                    result = c.fetchone()
                    ids = result[0]
                    name = result[1]
                    pts = int(round(result[2]))
                    joined_dic[t] = gettime()
                    elo_dic[t] = str(pts)
                    await ctx.channel.send(
                        name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS3))) + ")**")

            elif GAME3:
                await ctx.channel.send("You're still in a game.")

            if DRAFTING:
                await ctx.channel.send("Can't join a drafting lobby.")

            if warns > 2:
                await ctx.channel.send("You are banned.")
                return

            else:
                c.execute("SELECT currentg FROM players_team WHERE ID = ?", [t])
                B = c.fetchone()[0]
                if B is None:
                    if not RUNNING3:
                        t = ctx.message.author.id
                        t2 = ctx.author.id
                        conn = sqlite3.connect(db_path)
                        c = conn.cursor()
                        counter = 0
                        SKATER_LIST = []
                        RUNNING3 = True
                        GAME3 = True
                        STARTING3 = False
                        PLAYERS3.append(ids)
                        joined_dic[t] = gettime()
                        elo_dic[t] = str(pts)
                        await ctx.channel.send("Created a new lobby.")
                        await ctx.channel.send(
                            f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS3))) + ")**")

                        while len(PLAYERS3) < 6 and counter < 900000000:
                            # if STARTING:
                            #     STARTING = False
                            #     print("Not enough players.")
                            await asyncio.sleep(10)
                            counter += 1
                            if len(set(PLAYERS3)) > 5:
                                STARTING3 = True
                                counter -= 1
                                #await ctx.channel.send(f"Starting lobby **({gametype_lobby3[0]})** in **30** seconds.")
                                #await asyncio.sleep(0)
                            if len(set(PLAYERS3)) == 0 and counter > 6:
                                GAME3 = False
                                STARTING3 = False
                                RUNNING3 = False
                                return None

                        GAME3 = False
                        STARTING3 = False
                        if len(PLAYERS3) > 5:

                            np.random.shuffle(PLAYERS3)

                            ELOS = []
                            values = []
                            PLAYERS_AND_ELO = []
                            for t in PLAYERS3:
                                c.execute("SELECT elo, name FROM players_team WHERE ID = ?", [str(t)])
                                elo = c.fetchone()[0]
                                ELOS.append((t, int(elo)))
                                values.append(int(elo))

                            for t in PLAYERS3:
                                c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [str(t)])
                                fetch = c.fetchone()
                                players_name = fetch[0]
                                players_elo = fetch[1]
                                PLAYERS_AND_ELO.append(players_name)
                                PLAYERS_AND_ELO.append(players_elo)
                            mu = np.mean(values)
                            sigma = 300
                            mask = np.ones(len(PLAYERS3)).astype(bool)

                            counterb = 0

                            while(sum(mask) != 6) and counterb < 250000:
                                for k,x in enumerate(values):
                                    mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
                                counterb += 1

                            if sum(mask) == 6:
                                ELOS = list(np.array(ELOS)[mask])

                                team1 = sum([int(b[1]) for b in ELOS[0:3]])
                                team2 = sum([int(b[1]) for b in ELOS[3:6]])

                                diff = abs(team1-team2)

                                for t in itertools.permutations(ELOS, 6):
                                    team1 = sum([int(b[1]) for b in t[0:3]])
                                    team2 = sum([int(b[1]) for b in t[3:6]])
                                    if abs(team1 - team2) < diff:
                                        ELOS = t
                                        diff = abs(team1-team2)
                                c.execute("SELECT MAX(ID) from games_team")
                                gameID = c.fetchone()[0]
                                if gameID is None:
                                    gameID = 1
                                else:
                                    gameID = int(gameID) + 1

                                playerID = []
                                for t in ELOS:
                                    playerID.append(str(t[0]))

                                c.execute('INSERT INTO games_team VALUES(?, ?, ?, ?, ?, ?, ?, NULL, NULL, NULL,NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)

                                start = datetime.datetime.now()
                                time = start.strftime("%M")
                                time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")
                                c.execute("UPDATE games_team set start_time = ? WHERE ID = ?", [int(time), str(gameID)])
                                c.execute("UPDATE games_team SET gamedate = ? WHERE ID = ?", [time_data2[0] + " " + time_data2[1] + " " + time_data2[2],str(gameID)])

                                for t in playerID:
                                    c.execute("UPDATE players_team SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

                                capt = 0
                                captid = ""
                                finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:3]])) + "):** "
                                for k,t in enumerate(playerID):
                                    c.execute("SELECT name FROM players_team WHERE ID = ?", [str(t)])
                                    name = c.fetchone()[0]
                                    if(capt < int(ELOS[k][1])):
                                        capt = int(ELOS[k][1])
                                        captid = name
                                    finalstr += name + "   "
                                    if k == 1:
                                        finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[3:6]])) + "): **"
                                        capt = 0
                                        captid = ""

                                conn.commit()

                                notestr = ""
                                for t in playerID:
                                    notestr += "<@" + t + "> "

                                total_elo = team1 + team2
                                team1_percent = team1 / total_elo * 100
                                t1p = round(team1_percent)
                                team2_percent = team2 / total_elo * 100
                                t2p = round(team2_percent)
                                diff = np.abs(team1 - team2)
                                print(PLAYERS_AND_ELO)

                                player_1 = f"{PLAYERS_AND_ELO[0]} [{int(round(PLAYERS_AND_ELO[1]))}]"
                                player_2 = f"{PLAYERS_AND_ELO[2]} [{int(round(PLAYERS_AND_ELO[3]))}]"
                                player_3 = f"{PLAYERS_AND_ELO[4]} [{int(round(PLAYERS_AND_ELO[5]))}]"
                                player_4 = f"{PLAYERS_AND_ELO[6]} [{int(round(PLAYERS_AND_ELO[7]))}]"
                                player_5 = f"{PLAYERS_AND_ELO[8]} [{int(round(PLAYERS_AND_ELO[9]))}]"
                                player_6 = f"{PLAYERS_AND_ELO[10]} [{int(round(PLAYERS_AND_ELO[11]))}]"
                                                                                                                            

                                team_1_sum = PLAYERS_AND_ELO[1] + PLAYERS_AND_ELO[3] + PLAYERS_AND_ELO[5]
                                team_2_sum = PLAYERS_AND_ELO[7] + PLAYERS_AND_ELO[9] + PLAYERS_AND_ELO[11]

                                print(PLAYERS_AND_ELO[0])
                                print(PLAYERS_AND_ELO[2])
                                print(PLAYERS_AND_ELO[4])
                                print(PLAYERS_AND_ELO[6])
                                print(PLAYERS_AND_ELO[8])
                                print(PLAYERS_AND_ELO[10])

                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[0]])
                                p1 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[2]])
                                p2 = c.fetchone()[0]

                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[4]])
                                p3 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[6]])
                                p4 = c.fetchone()[0]

                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[8]])
                                p5 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS_TEAM WHERE NAME = ?", [PLAYERS_AND_ELO[10]])
                                p6 = c.fetchone()[0]

                                game_dict = {}
                                game_dict["ids"] = [p1, p2, p3, p4, p5, p6]
                                game_dict["teams"] = [[p1, p2, p3], [p4, p5, p6]]
                                game_dict["player_to_team"] = {}
                                for i, team in enumerate(game_dict["teams"]):
                                    for player in team:
                                        game_dict["player_to_team"][player] = i
                                game_dict["player_votes"] = defaultdict(str)
                                game_dict["vote_count"] = 0
                                game_dict["won"] = [0, 0, 0]
                                game_dict["lost"] = [0, 0, 0]
                                game_dict["draw"] = [0, 0, 0]
                                global_dict[gameID] = game_dict

                                final = f"**Game #{gameID} started:**\n**Team 1 ({int(round(team_1_sum))}):** {player_1}, {player_2}, {player_3}\n**Team 2 ({int(round(team_2_sum))}):** {player_4}, {player_5}, {player_6}\nTotal ELO Difference: {diff}.\nTeam 1: {t1p}% probability to win;Team 2: {t2p}% probability to win."

                                # finalstr += "\nTotal ELO Difference: " + str(diff) + "."
                                # finalstr += f"\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
                                guild = discord.utils.get(client.guilds, id=383292703955222542)
                                lobby_channel = discord.utils.get(guild.channels, id=790313624395972668)
                                await lobby_channel.send(f"{final}\n{notestr}")

                                conn.commit()
                                
                                PLAYERS3 = []

                            else:
                                await ctx.channel.send("Could not balance lobby.")
                                PLAYERS3 = []
                        else:
                            await ctx.channel.send("Not Enough Players")
                            PLAYERS3 = []

                        PLAYERS3 = []
                        RUNNING3 = False
                        gametype_lobby3 = []

                        conn.close()

    # if ctx.channel.id == ones_channel.id:

    #     x = ctx.author
    #     t = ctx.message.author.id
    #     n = ctx.message.author.name
    #     member = ctx.author
    #     date = datetime.datetime.now()
    #     profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"
    #     conn = sqlite3.connect(db_path, uri=True)
    #     c = conn.cursor()
    #     c.execute("SELECT elo FROM players WHERE ID = ?", [t])
    #     mon = c.fetchone()

    #     if mon == None:
    #         c.execute('INSERT INTO players VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
    #                 [t, n, "Empty", date, str(profile)])
    #         c.execute("INSERT INTO warnings VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [t,n])
    #         await ctx.channel.send("You are now registered.")
    #         role = discord.utils.get(ctx.guild.roles, name="League")
    #         await member.add_roles(role)
    #         conn.commit()

    #     c.execute("SELECT ID, name, elo, fresh_warns FROM players where ID = ?", [t])
    #     creator = ctx.message.author.name
    #     results = c.fetchone()
    #     ids = results[0]
    #     pts = int(round(results[2]))
    #     warns = results[3]

    #     c = conn.cursor()

    #     c.execute("SELECT currentg FROM players WHERE ID = ?", [t])

    #     A = c.fetchone()[0] is None

    #     if gametype == None:

    #         gametype_lobby = []
    #         gametype_lobby.append("normal")

    #         if t in PLAYERS:
    #             await ctx.channel.send("You're already in the lobby.")
    #             return

    #         if GAME and A:

    #             if warns > 2:
    #                 await ctx.send("You are currently banned.")
    #                 return

    #             else:

    #                 PLAYERS.append(t)
    #                 c.execute("SELECT ID, name, elo FROM players where ID = ?", [t])
    #                 result = c.fetchone()
    #                 ids = result[0]
    #                 name = result[1]
    #                 pts = int(round(result[2]))
    #                 joined_dic[t] = gettime()
    #                 elo_dic[t] = str(pts)
    #                 await ctx.channel.send(
    #                     name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS))) + ")**")

    #         elif GAME:
    #             await ctx.channel.send("You're still in a game.")

    #         if DRAFTING:
    #             await ctx.channel.send("Can't join a drafting lobby.")

    #         if warns > 2:
    #             await ctx.channel.send("You are banned.")
    #             return

    #         else:
    #             c.execute("SELECT currentg FROM players WHERE ID = ?", [t])
    #             B = c.fetchone()[0]
    #             if B is None:
    #                 if not RUNNING:
    #                     t = ctx.message.author.id
    #                     t2 = ctx.author.id
    #                     conn = sqlite3.connect(db_path)
    #                     c = conn.cursor()
    #                     counter = 0
    #                     SKATER_LIST = []
    #                     RUNNING = True
    #                     GAME = True
    #                     STARTING = False
    #                     PLAYERS.append(ids)
    #                     joined_dic[t] = gettime()
    #                     elo_dic[t] = str(pts)
    #                     await ctx.channel.send("Created a new lobby.")
    #                     await ctx.channel.send(
    #                         f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS))) + ")**")

    #                     while len(PLAYERS) < 2 and counter < 900000000:
    #                         if STARTING:
    #                             STARTING = False
    #                             print("Not enough players.")
    #                         await asyncio.sleep(10)
    #                         counter += 1
    #                         if len(set(PLAYERS)) > 2:
    #                             STARTING = True
    #                             counter -= 1
    #                             #await ctx.channel.send(f"Starting lobby {gametype} in **30** seconds.")
    #                             #await asyncio.sleep(30)
    #                         if len(set(PLAYERS)) == 0 and counter > 6:
    #                             GAME = False
    #                             STARTING = False
    #                             RUNNING = False
    #                             return None

    #                     GAME = False
    #                     STARTING = False
    #                     if len(PLAYERS) > 1:

    #                         np.random.shuffle(PLAYERS)

    #                         ELOS = []
    #                         values = []
    #                         PLAYERS_AND_ELO = []
    #                         for t in PLAYERS:
    #                             c.execute("SELECT elo, name FROM players WHERE ID = ?", [str(t)])
    #                             elo = c.fetchone()[0]
    #                             ELOS.append((t, int(elo)))
    #                             values.append(int(elo))

    #                         for t in PLAYERS:
    #                             c.execute("SELECT name, elo FROM players WHERE ID = ?", [str(t)])
    #                             fetch = c.fetchone()
    #                             players_name = fetch[0]
    #                             players_elo = fetch[1]
    #                             PLAYERS_AND_ELO.append(players_name)
    #                             PLAYERS_AND_ELO.append(players_elo)

    #                         mu = np.mean(values)
    #                         sigma = 300
    #                         mask = np.ones(len(PLAYERS)).astype(bool)

    #                         counterb = 0

    #                         while(sum(mask) != 2) and counterb < 250000:
    #                             for k,x in enumerate(values):
    #                                 mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
    #                             counterb += 1

    #                         if sum(mask) == 2:
    #                             ELOS = list(np.array(ELOS)[mask])

    #                             team1 = sum([int(b[1]) for b in ELOS[0:1]])
    #                             team2 = sum([int(b[1]) for b in ELOS[1:2]])

    #                             diff = abs(team1-team2)

    #                             for t in itertools.permutations(ELOS, 2):
    #                                 team1 = sum([int(b[1]) for b in t[0:1]])
    #                                 team2 = sum([int(b[1]) for b in t[1:2]])
    #                                 if abs(team1 - team2) < diff:
    #                                     ELOS = t
    #                                     diff = abs(team1-team2)
    #                             c.execute("SELECT MAX(ID) from games")
    #                             gameID = c.fetchone()[0]
    #                             if gameID is None:
    #                                 gameID = 1
    #                             else:
    #                                 gameID = int(gameID) + 1

    #                             playerID = []
    #                             for t in ELOS:
    #                                 playerID.append(str(t[0]))

    #                             c.execute('INSERT INTO games VALUES(?, ?, ?, NULL, NULL, NULL, NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)
    #                             start = datetime.datetime.now()
    #                             time = start.strftime("%M")
    #                             time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")
    #                             c.execute("UPDATE GAMES set start_time = ? WHERE ID = ?", [int(time), str(gameID)])
    #                             c.execute("UPDATE GAMES SET gamedate = ? WHERE ID = ?", [time_data2[0] + " " + time_data2[1] + " " + time_data2[2],str(gameID)])

    #                             for t in playerID:
    #                                 c.execute("UPDATE players SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

    #                             capt = 0
    #                             captid = ""
    #                             finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:1]])) + "):** "
    #                             for k,t in enumerate(playerID):
    #                                 c.execute("SELECT name FROM players WHERE ID = ?", [str(t)])
    #                                 name = c.fetchone()[0]
    #                                 if(capt < int(ELOS[k][1])):
    #                                     capt = int(ELOS[k][1])
    #                                     captid = name
    #                                 finalstr += name + "   "
    #                                 if k == 0:
    #                                     finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[1:2]])) + "): **"
    #                                     capt = 0
    #                                     captid = ""

    #                             notestr = ""
    #                             for t in playerID:
    #                                 notestr += "<@" + t + "> "

    #                             total_elos = team1 + team2
    #                             team1_percentage = np.floor(team1 / total_elos * 100)
    #                             t1pp = round(team1_percentage)
    #                             team2_percentage = np.floor(team2 / total_elos * 100)
    #                             t2pp = round(team2_percentage)
    #                             diffe = np.abs(team1 - team2)

    #                             player_1 = f"{PLAYERS_AND_ELO[0]} [{int(round(PLAYERS_AND_ELO[1]))}]"
    #                             player_2 = f"{PLAYERS_AND_ELO[2]} [{int(round(PLAYERS_AND_ELO[3]))}]"

    #                             team_1_sum = PLAYERS_AND_ELO[1]
    #                             team_2_sum = PLAYERS_AND_ELO[3]

    #                             final = f"**Game #{gameID} started:**\n**Team 1 ({int(round(team_1_sum))}):** {player_1}\n**Team 2 ({int(round(team_2_sum))}):** {player_2}\nTotal ELO Difference: {diff}.\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."

    #                             # finalstr += "\nTotal ELO Difference: " + str(diff) + "."
    #                             # finalstr += f"\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
    #                             guild = discord.utils.get(client.guilds, id=784960512534380586)
    #                             lobby_channel = discord.utils.get(guild.channels, id=785009271317463091)
    #                             await lobby_channel.send(f"{final}\n{notestr}")

    #                             conn.commit()

    #                             PLAYERS = []

    #                         else:
    #                             await ctx.channel.send("Could not balance lobby.")
    #                             PLAYERS = []
    #                     else:
    #                         await ctx.channel.send("Not Enough Players")
    #                         PLAYERS = []

    #                     PLAYERS = []
    #                     RUNNING = False
    #                     gametype_lobby = []

    #                     conn.close()

    if ctx.channel.id == ones_channel.id:

        x = ctx.author
        t = ctx.message.author.id
        n = ctx.message.author.name
        member = ctx.author
        date = datetime.datetime.now()
        profile = "https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg"
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        c.execute("SELECT elo FROM players WHERE ID = ?", [t])
        mon = c.fetchone()

        if mon == None:
            c.execute('INSERT INTO players VALUES(?, ?, 0, 0, 1500, NULL, 0, 0, 0, 0, ?, 0, ?, 0, ?, NULL, 400)',
                    [t, n, "Empty", date, str(profile)])
            c.execute("INSERT INTO warnings VALUES(?,?,NULL,NULL,NULL,NULL,NULL,NULL)", [t,n])
            await ctx.channel.send("You are now registered.")
            role = discord.utils.get(ctx.guild.roles, name="League")
            await member.add_roles(role)
            conn.commit()

        c.execute("SELECT ID, name, elo, fresh_warns FROM players where ID = ?", [t])
        creator = ctx.message.author.name
        results = c.fetchone()
        ids = results[0]
        pts = int(round(results[2]))
        warns = results[3]

        c = conn.cursor()

        c.execute("SELECT currentg FROM players WHERE ID = ?", [t])
        Y = c.fetchone()[0]
        if Y is not None:
            await ctx.send("You're still in a game.")
            return

        c.execute("SELECT currentg FROM players WHERE ID = ?", [t])
        A = c.fetchone()[0] is None

        if gametype == None:

            gametype_lobby = []
            gametype_lobby.append("normal")

            if t in PLAYERS:
                await ctx.channel.send("You're already in the lobby.")
                return

            if GAME and A:

                if warns > 2:
                    await ctx.send("You are currently banned.")
                    return

                else:

                    PLAYERS.append(t)
                    c.execute("SELECT ID, name, elo FROM players where ID = ?", [t])
                    result = c.fetchone()
                    ids = result[0]
                    name = result[1]
                    pts = int(round(result[2]))
                    joined_dic[t] = gettime()
                    elo_dic[t] = str(pts)
                    await ctx.channel.send(
                        name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS))) + ")**")

            elif GAME:
                await ctx.channel.send("You're still in a game.")

            if DRAFTING:
                await ctx.channel.send("Can't join a drafting lobby.")

            if warns > 2:
                await ctx.channel.send("You are banned.")
                return

            else:
                c.execute("SELECT currentg FROM players WHERE ID = ?", [t])
                B = c.fetchone()[0]
                if B is None:
                    if not RUNNING:
                        t = ctx.message.author.id
                        t2 = ctx.author.id
                        conn = sqlite3.connect(db_path)
                        c = conn.cursor()
                        counter = 0
                        SKATER_LIST = []
                        RUNNING = True
                        GAME = True
                        STARTING = False
                        PLAYERS.append(ids)
                        joined_dic[t] = gettime()
                        elo_dic[t] = str(pts)
                        await ctx.channel.send("Created a new lobby.")
                        await ctx.channel.send(
                            f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS))) + ")**")

                        while len(PLAYERS) < 2 and counter < 900000000:
                            if STARTING:
                                STARTING = False
                                print("Not enough players.")
                            await asyncio.sleep(10)
                            counter += 1
                            if len(set(PLAYERS)) > 2:
                                STARTING = True
                                counter -= 1
                                #await ctx.channel.send(f"Starting lobby {gametype} in **30** seconds.")
                                #await asyncio.sleep(30)
                            if len(set(PLAYERS)) == 0 and counter > 6:
                                GAME = False
                                STARTING = False
                                RUNNING = False
                                return None

                        GAME = False
                        STARTING = False
                        if len(PLAYERS) > 1:

                            np.random.shuffle(PLAYERS)

                            ELOS = []
                            values = []
                            PLAYERS_AND_ELO = []
                            for t in PLAYERS:
                                c.execute("SELECT elo, name FROM players WHERE ID = ?", [str(t)])
                                elo = c.fetchone()[0]
                                ELOS.append((t, int(elo)))
                                values.append(int(elo))

                            for t in PLAYERS:
                                c.execute("SELECT name, elo FROM players WHERE ID = ?", [str(t)])
                                fetch = c.fetchone()
                                players_name = fetch[0]
                                players_elo = fetch[1]
                                PLAYERS_AND_ELO.append(players_name)
                                PLAYERS_AND_ELO.append(players_elo)

                            mu = np.mean(values)
                            sigma = 300
                            mask = np.ones(len(PLAYERS)).astype(bool)

                            counterb = 0

                            while(sum(mask) != 2) and counterb < 250000:
                                for k,x in enumerate(values):
                                    mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
                                counterb += 1

                            if sum(mask) == 2:
                                ELOS = list(np.array(ELOS)[mask])

                                team1 = sum([int(b[1]) for b in ELOS[0:1]])
                                team2 = sum([int(b[1]) for b in ELOS[1:2]])

                                diff = abs(team1-team2)

                                for t in itertools.permutations(ELOS, 2):
                                    team1 = sum([int(b[1]) for b in t[0:1]])
                                    team2 = sum([int(b[1]) for b in t[1:2]])
                                    if abs(team1 - team2) < diff:
                                        ELOS = t
                                        diff = abs(team1-team2)
                                c.execute("SELECT MAX(ID) from games")
                                gameID = c.fetchone()[0]
                                if gameID is None:
                                    gameID = 1
                                else:
                                    gameID = int(gameID) + 1

                                playerID = []
                                for t in ELOS:
                                    playerID.append(str(t[0]))

                                c.execute('INSERT INTO games VALUES(?, ?, ?, NULL, NULL, NULL, NULL, NULL,NULL,NULL,NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)
                                start = datetime.datetime.now()
                                time = start.strftime("%M")
                                time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")
                                c.execute("UPDATE GAMES set start_time = ? WHERE ID = ?", [int(time), str(gameID)])
                                c.execute("UPDATE GAMES SET gamedate = ? WHERE ID = ?", [time_data2[0] + " " + time_data2[1] + " " + time_data2[2],str(gameID)])

                                for t in playerID:
                                    c.execute("UPDATE players SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

                                capt = 0
                                captid = ""
                                finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:1]])) + "):** "
                                for k,t in enumerate(playerID):
                                    c.execute("SELECT name FROM players WHERE ID = ?", [str(t)])
                                    name = c.fetchone()[0]
                                    if(capt < int(ELOS[k][1])):
                                        capt = int(ELOS[k][1])
                                        captid = name
                                    finalstr += name + "   "
                                    if k == 0:
                                        finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[1:2]])) + "): **"
                                        capt = 0
                                        captid = ""

                                notestr = ""
                                for t in playerID:
                                    notestr += "<@" + t + "> "

                                total_elos = team1 + team2
                                team1_percentage = np.floor(team1 / total_elos * 100)
                                t1pp = round(team1_percentage)
                                team2_percentage = np.floor(team2 / total_elos * 100)
                                t2pp = round(team2_percentage)
                                diffe = np.abs(team1 - team2)

                                player_1 = f"{PLAYERS_AND_ELO[0]} [{int(round(PLAYERS_AND_ELO[1]))}]"
                                player_2 = f"{PLAYERS_AND_ELO[2]} [{int(round(PLAYERS_AND_ELO[3]))}]"

                                team_1_sum = PLAYERS_AND_ELO[1]
                                team_2_sum = PLAYERS_AND_ELO[3]

                                final = f"**Game #{gameID} started:**\n**Team 1 ({int(round(team_1_sum))}):** {player_1}\n**Team 2 ({int(round(team_2_sum))}):** {player_2}\nTotal ELO Difference: {diff}.\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
                                
                                p1name = PLAYERS_AND_ELO[0]
                                p2name = PLAYERS_AND_ELO[2]

                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [p1name])
                                p1 = c.fetchone()[0]
                                
                                c.execute("SELECT ID FROM PLAYERS WHERE NAME = ?", [p2name])
                                p2 = c.fetchone()[0]

                                game_dict = {}
                                game_dict["ids"] = [p1, p2]
                                game_dict["teams"] = [[p1], [p2]]
                                game_dict["player_to_team"] = {p1: 0, p2: 1}
                                game_dict["player_votes"] = defaultdict(str)
                                game_dict["vote_count"] = 0
                                game_dict["won"] = [0, 0, 0]
                                game_dict["lost"] = [0, 0, 0]
                                game_dict["draw"] = [0, 0, 0]
                                global_dict[gameID] = game_dict

                                guild = discord.utils.get(client.guilds, id=383292703955222542)
                                lobby_channel = discord.utils.get(guild.channels, id=790313550270693396)
                                await lobby_channel.send(f"{final}\n{notestr}")

                                conn.commit()

                                PLAYERS = []

                            else:
                                await ctx.channel.send("Could not balance lobby.")
                                PLAYERS = []
                        else:
                            await ctx.channel.send("Not Enough Players")
                            PLAYERS = []

                        PLAYERS = []
                        RUNNING = False
                        gametype_lobby = []

                        conn.close()

        if gametype == "4v4":

            gametype_lobby = []
            gametype_lobby.append("4v4")

            if t in PLAYERS:
                await ctx.channel.send("You're already in the lobby.")
                return

            if GAME and A:

                if warns > 2:
                    await ctx.send("You are currently banned.")
                    return

                else:

                    PLAYERS.append(t)
                    c.execute("SELECT ID, name, elo FROM players where ID = ?", [t])
                    result = c.fetchone()
                    ids = result[0]
                    name = result[1]
                    pts = int(round(result[2]))
                    joined_dic[t] = gettime()
                    elo_dic[t] = str(pts)
                    await ctx.channel.send(
                        name + " **[" + str(pts) + "]** has joined the lobby. **(" + str(len(set(PLAYERS))) + ")**")

            elif GAME:
                await ctx.channel.send("You're still in a game.")

            if DRAFTING:
                await ctx.channel.send("Can't join a drafting lobby.")

            if warns > 2:
                await ctx.channel.send("You are banned.")
                return

            else:
                c.execute("SELECT currentg FROM players WHERE ID = ?", [t])
                B = c.fetchone()[0]
                if B is None:
                    if not RUNNING:
                        t = ctx.message.author.id
                        t2 = ctx.author.id
                        conn = sqlite3.connect(db_path)
                        c = conn.cursor()
                        counter = 0
                        SKATER_LIST = []
                        RUNNING = True
                        GAME = True
                        STARTING = False
                        PLAYERS.append(ids)
                        joined_dic[t] = gettime()
                        elo_dic[t] = str(pts)
                        await ctx.channel.send("Created a new lobby.")
                        await ctx.channel.send(
                            f"**{creator} [{pts}]** has joined the lobby! **(" + str(len(set(PLAYERS))) + ")**")

                        while len(PLAYERS) < 8 and counter < 900000000:
                            if STARTING:
                                STARTING = False
                                print("Not enough players.")
                            await asyncio.sleep(10)
                            counter += 1
                            if len(set(PLAYERS)) > 7:
                                STARTING = True
                                counter -= 1
                                await ctx.channel.send("Game starting in **30** seconds...")
                                await asyncio.sleep(30)
                            if len(set(PLAYERS)) == 0 and counter > 6:
                                GAME = False
                                STARTING = False
                                RUNNING = False
                                return None

                        GAME = False
                        STARTING = False
                        if len(PLAYERS) > 7:

                            np.random.shuffle(PLAYERS)

                            ELOS = []
                            values = []
                            PLAYERS_AND_ELO = []
                            for t in PLAYERS:
                                c.execute("SELECT elo, name FROM players WHERE ID = ?", [str(t)])
                                elo = c.fetchone()[0]
                                ELOS.append((t, int(elo)))
                                values.append(int(elo))

                            for t in PLAYERS:
                                c.execute("SELECT name, elo FROM players WHERE ID = ?", [str(t)])
                                fetch = c.fetchone()
                                players_name = fetch[0]
                                players_elo = fetch[1]
                                PLAYERS_AND_ELO.append(players_name)
                                PLAYERS_AND_ELO.append(players_elo)

                            mu = np.mean(values)
                            sigma = 300
                            mask = np.ones(len(PLAYERS)).astype(bool)

                            counterb = 0

                            while(sum(mask) != 8) and counterb < 250000:
                                for k,x in enumerate(values):
                                    mask[k] = np.random.uniform(0.0,1.0) < 1.0/2.0*(1.0+scipy.special.erf((x-mu)/(sigma*np.sqrt(2))))
                                counterb += 1

                            if sum(mask) == 8:
                                ELOS = list(np.array(ELOS)[mask])

                                team1 = sum([int(b[1]) for b in ELOS[0:4]])
                                team2 = sum([int(b[1]) for b in ELOS[4:8]])

                                diff = abs(team1-team2)

                                for t in itertools.permutations(ELOS, 8):
                                    team1 = sum([int(b[1]) for b in t[0:4]])
                                    team2 = sum([int(b[1]) for b in t[4:8]])
                                    if abs(team1 - team2) < diff:
                                        ELOS = t
                                        diff = abs(team1-team2)
                                c.execute("SELECT MAX(ID) from games")
                                gameID = c.fetchone()[0]
                                if gameID is None:
                                    gameID = 1
                                else:
                                    gameID = int(gameID) + 1

                                playerID = []
                                for t in ELOS:
                                    playerID.append(str(t[0]))

                                c.execute('INSERT INTO games VALUES(?, ?, ?, NULL, NULL, NULL, NULL, NULL,NULL,NULL,NULL)', [str(gameID)] + playerID)

                                start = datetime.datetime.now()
                                time = start.strftime("%M")
                                c.execute("UPDATE GAMES set start_time = ? WHERE ID = ?", [int(time), str(gameID)])

                                for t in playerID:
                                    c.execute("UPDATE players SET currentg = ? WHERE ID = ?", [str(gameID), str(t)])

                                capt = 0
                                captid = ""
                                finalstr = "**Game #" + str(gameID) + " started**:\n**Team 1 (" + str(sum([int(b[1]) for b in ELOS[0:4]])) + "):** "
                                for k,t in enumerate(playerID):
                                    c.execute("SELECT name FROM players WHERE ID = ?", [str(t)])
                                    name = c.fetchone()[0]
                                    if(capt < int(ELOS[k][1])):
                                        capt = int(ELOS[k][1])
                                        captid = name
                                    finalstr += name + "   "
                                    if k == 3:
                                        finalstr += "\n**Team 2 (" + str(sum([int(b[1])for b in ELOS[4:8]])) + "): **"
                                        capt = 0
                                        captid = ""

                                notestr = ""
                                for t in playerID:
                                    notestr += "<@" + t + "> "

                                total_elos = team1 + team2
                                team1_percentage = np.floor(team1 / total_elos * 100)
                                t1pp = round(team1_percentage)
                                team2_percentage = np.floor(team2 / total_elos * 100)
                                t2pp = round(team2_percentage)
                                diffe = np.abs(team1 - team2)

                                player_1 = f"{PLAYERS_AND_ELO[0]} [{PLAYERS_AND_ELO[1]}]"
                                player_2 = f"{PLAYERS_AND_ELO[2]} [{PLAYERS_AND_ELO[3]}]"
                                player_3 = f"{PLAYERS_AND_ELO[4]} [{PLAYERS_AND_ELO[5]}]"
                                player_4 = f"{PLAYERS_AND_ELO[6]} [{PLAYERS_AND_ELO[7]}]"
                                player_5 = f"{PLAYERS_AND_ELO[8]} [{PLAYERS_AND_ELO[9]}]"
                                player_6 = f"{PLAYERS_AND_ELO[10]} [{PLAYERS_AND_ELO[11]}]"
                                player_7 = f"{PLAYERS_AND_ELO[12]} [{PLAYERS_AND_ELO[13]}]"
                                player_8 = f"{PLAYERS_AND_ELO[14]} [{PLAYERS_AND_ELO[15]}]"

                                team_1_sum = PLAYERS_AND_ELO[1] + PLAYERS_AND_ELO[3] + PLAYERS_AND_ELO[5] + PLAYERS_AND_ELO[7]
                                team_2_sum = PLAYERS_AND_ELO[9] + PLAYERS_AND_ELO[11] + PLAYERS_AND_ELO[13] + PLAYERS_AND_ELO[15]

                                final = f"**Game #{gameID} started:**\n**Team 1 ({team_1_sum}):** {player_1}, {player_2}, {player_3}, {player_4}\n**Team 2 ({team_2_sum}):** {player_5}, {player_6}, {player_7}, {player_8}\nTotal ELO Difference: {diff}.\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."

                                # finalstr += "\nTotal ELO Difference: " + str(diff) + "."
                                # finalstr += f"\nTeam 1: {t1pp}% probability to win;Team 2: {t2pp}% probability to win."
                                guild = discord.utils.get(client.guilds, id=784960512534380586)
                                lobby_channel = discord.utils.get(guild.channels, id=785009271317463091)
                                await lobby_channel.send(f"{final}\n{notestr}")

                                conn.commit()

                                PLAYERS = []

                            else:
                                await ctx.channel.send("Could not balance lobby.")
                                PLAYERS = []
                        else:
                            await ctx.channel.send("Not Enough Players")
                            PLAYERS = []

                        PLAYERS = []
                        RUNNING = False
                        gametype_lobby = []

                        conn.close()


@client.command(aliases=["p"])
@commands.has_role("Captain")
async def draft(ctx, player):
    """ Picks a player for your team if you're the captain."""

    global TURN, GAME, PLAYERS, TEAMS, DRAFTING_ELOS, db_path

    if ctx.channel.id == na_draft_channel.id:
            
        if len(TEAMS) > 1 and (len(TEAMS[0]) < 4 or len(TEAMS[1]) < 4):
            captain = str(ctx.message.author.id)
            conn = sqlite3.connect(db_path, uri=True)
            c = conn.cursor()
            player = find_userid_by_name(ctx, player)
            if player is None:
                await ctx.channel.send("No player found by that name.")
                return
            if player not in PLAYERS:
                await ctx.channel.send("No player found by that name.")
                return
            c.execute("SELECT name, ID, elo FROM players WHERE ID = ?", [player])
            user = c.fetchone()
            name = user[0]
            ids = user[1]
            elo = user[2]

            if captain == TURN:
                if str(TEAMS[0][0][0]) == TURN:
                    turn_name = str(TEAMS[0][0][1])
                    TEAMS[0].append((user[1], user[0], user[2]))
                    PLAYERS.remove(player)
                    DRAFTING_ELOS.remove((int(ids), int(elo), str(name)))
                    if (len(TEAMS[0]) > len(TEAMS[1])):
                        TURN = str(TEAMS[1][0][0])
                        turn_name = str(TEAMS[1][0][1])

                    if len(TEAMS[1]) < 4 or len(TEAMS[0]) < 4:

                        if len(DRAFTING_ELOS) is 1:
                            last_player_id = DRAFTING_ELOS[0][0]
                            c.execute("SELECT id, elo, name FROM players WHERE ID = ?", [str(last_player_id)])
                            last_player = c.fetchone()
                            ids2 = last_player[0]
                            elo2 = last_player[1]
                            name2 = last_player[2]
                            TEAMS[1].append((ids2, name2, elo2))
                            return

                        player_string = []

                        for player in DRAFTING_ELOS:
                            player_string.append(f"{player[2]} [{player[1]}]")

                        await ctx.send('Players: ' + ', '.join(player_string))
                        await ctx.channel.send("<@" + str(TURN) + "> .draft player")          

                elif str(TEAMS[1][0][0]) == TURN:
                    turn_name = str(TEAMS[1][0][1])
                    TEAMS[1].append((user[1], user[0], user[2]))
                    PLAYERS.remove(player)
                    DRAFTING_ELOS.remove((int(ids), int(elo), str(name)))
                    if (len(TEAMS[1]) > len(TEAMS[0])):
                        TURN = str(TEAMS[0][0][0])
                        turn_name = str(TEAMS[0][0][1])
                    if len(TEAMS[1]) < 4 or len(TEAMS[0]) < 4:

                        if len(DRAFTING_ELOS) is 1:
                            last_player_id = DRAFTING_ELOS[0][0]
                            c.execute("SELECT id, elo, name FROM players WHERE ID = ?", [str(last_player_id)])
                            last_player = c.fetchone()
                            ids2 = last_player[0]
                            elo2 = last_player[1]
                            name2 = last_player[2]
                            TEAMS[0].append((ids2, name2, elo2))
                            return

                        player_string = []
                        for player in DRAFTING_ELOS:
                            player_string.append(f"{player[2]} [{player[1]}]")
                            
                        await ctx.send('Players: ' + ', '.join(player_string))
                        await ctx.channel.send("<@" + str(TURN) + "> .draft player")

            else:
                await ctx.channel.send("It's not your turn.")

        else:
            await ctx.channel.send("No game started.")


@client.command(aliases=["l"])
@commands.cooldown(1, 5, commands.BucketType.user)
async def leave(ctx):
    '''Removes user from both lobby.'''

    global PLAYERS, PLAYERS2, PLAYERS3, db_path

    if ctx.channel.id == ones_channel.id:

        t = ctx.message.author.id

        conn = sqlite3.connect(db_path, uri=True)

        c = conn.cursor()

        if ctx.message.channel.id == ones_channel.id:
            if GAME:
                try:
                    PLAYERS = list(set(PLAYERS))
                    PLAYERS.remove(ctx.message.author.id)
                    c.execute("SELECT name, elo FROM players where ID = ?", [t])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(result[1]))
                    await ctx.channel.send(
                        name + "** [" + str(pts) + "]** has removed their signup! **(" + str(len(set(PLAYERS))) + ")**")
                    # await ctx.channel.edit(topic="Open Lobby (" + str(len(set(PLAYERS))) + "/8)", reason=None)
                except:
                    True
            else:
                await ctx.channel.send("You're not in a lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        t = ctx.message.author.id

        conn = sqlite3.connect(db_path, uri=True)

        c = conn.cursor()

        if ctx.message.channel.id == twos_channel.id:
            if GAME2:
                try:
                    PLAYERS2 = list(set(PLAYERS2))
                    PLAYERS2.remove(ctx.message.author.id)
                    c.execute("SELECT name, elo FROM players where ID = ?", [t])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(results[1]))
                    await ctx.channel.send(
                        name + "** [" + str(pts) + "]** has removed their signup! **(" + str(len(set(PLAYERS2))) + ")**")
                    # await ctx.channel.edit(topic="Open Lobby (" + str(len(set(PLAYERS))) + "/8)", reason=None)
                except:
                    True
            else:
                await ctx.channel.send("You're not in a lobby.")

        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:

        t = ctx.message.author.id

        conn = sqlite3.connect(db_path, uri=True)

        c = conn.cursor()

        if ctx.message.channel.id == threes_channel.id:
            if GAME3:
                try:
                    PLAYERS3 = list(set(PLAYERS3))
                    PLAYERS3.remove(ctx.message.author.id)
                    c.execute("SELECT name, elo FROM players where ID = ?", [t])
                    result = c.fetchone()
                    name = result[0]
                    pts = int(round(result[1]))
                    await ctx.channel.send(
                        name + "** [" + str(pts) + "]** has removed their signup! **(" + str(len(set(PLAYERS3))) + ")**")
                    # await ctx.channel.edit(topic="Open Lobby (" + str(len(set(PLAYERS))) + "/8)", reason=None)
                except:
                    True
            else:
                await ctx.channel.send("You're not in a lobby.")

        conn.commit()
        conn.close()


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def ban(ctx, name, *, reason):
    '''Bans a user from the channel.'''

    global joined_dic

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()   
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        activity_channel = ctx.guild.get_channel(790313358816968715)
        n = ctx.author.name
        t = find_userid_by_name(ctx, name)
        reasons = "{}".format(reason)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return
        c.execute("SELECT name, ID FROM players where ID = ?", [t])
        player = c.fetchone()
        names = player[0]
        ids = player[1]
        member = ctx.guild.get_member(ids)
        banned_role = discord.utils.get(ctx.guild.roles, name="Banned")
        await member.add_roles(banned_role)
        banjo_role = discord.utils.get(ctx.guild.roles, name="Banjo")
        await member.remove_roles(banjo_role)
        await ctx.send("**" + str(names) + "** was banned for " + str(reasons) + " by **" + str(n) + "**.")
        await activity_channel.send("**" + str(names) + "** was banned for " + str(reasons) + " by **" + str(n) + "**.")


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def unban(ctx, name):
    '''Unbans a user from the channel.'''

    global joined_dic

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()     
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        n = ctx.author.name
        activity_channel = ctx.guild.get_channel(790313358816968715)
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return
        c.execute("SELECT name, ID FROM players where ID = ?", [t])
        player = c.fetchone()
        names = player[0]
        ids = player[1]
        member = ctx.guild.get_member(ids)
        banned_role = discord.utils.get(ctx.guild.roles, name="Banned")
        await member.remove_roles(banned_role)
        banjo_role = discord.utils.get(ctx.guild.roles, name="Banjo")
        await member.add_roles(banjo_role)
        await ctx.send("**" + str(names) + "** was unbanned by **" + str(n) + "**.")
        await activity_channel.send("**" + str(names) + "** was unbanned by **" + str(n) + "**.")


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def mute(ctx, name):
    '''Mutes a user from the channel.'''
    
    global joined_dic

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        activity_channel = ctx.guild.get_channel(790313358816968715)
        n = ctx.author.name
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return
        c.execute("SELECT name, ID FROM players where ID = ?", [t])
        player = c.fetchone()
        names = player[0]
        ids = player[1]
        member = ctx.guild.get_member(ids)
        banjo_role = discord.utils.get(ctx.guild.roles, name="League")
        await member.remove_roles(banjo_role)
        muted_role = discord.utils.get(ctx.guild.roles, name="Muted")
        await member.add_roles(muted_role)
        await ctx.send("**" + str(names) + "** was muted by **" + str(n) + "**.")
        await activity_channel.send("**" + str(names) + "** was muted by **" + str(n) + "**.")


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin')
async def unmute(ctx, name):
    '''Unmutes a user from the channel.'''

    global joined_dic

    if ctx.channel.id == na_lobby_channel.id or ctx.channel.id == admin_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        n = ctx.author.name
        activity_channel = ctx.guild.get_channel(790313358816968715)
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return
        c.execute("SELECT name, ID FROM players where ID = ?", [t])
        player = c.fetchone()
        names = player[0]
        ids = player[1]
        member = ctx.guild.get_member(ids)
        muted_role = discord.utils.get(ctx.guild.roles, name="Muted")
        await member.remove_roles(muted_role)
        banjo_role = discord.utils.get(ctx.guild.roles, name="League")
        await member.add_roles(banjo_role)
        await ctx.send("**" + str(names) + "** was unmuted by **" + str(n) + "**.")
        await activity_channel.send("**" + str(names) + "** was unmuted by **" + str(n) + "**.")

@client.command()
@commands.has_any_role('League Admin')
async def reset_votes(ctx):

    global draw_votes, won_votes, lost_votes, voting_list, solo_won, solo_lost, team_won, team_lost, won_vote_names, lost_vote_names, draw_vote_names, draw_votes2, won_votes2, lost_votes2, team_won2, team_lost2, won_vote_names2, lost_vote_names2, draw_vote_names2, draw_votes3, won_votes3, lost_votes3, team_won3, team_lost3, won_vote_names3, lost_vote_names3, draw_vote_names3

    if ctx.channel.id == ones_channel.id:
        draw_votes = 0
        won_votes = 0
        lost_votes = 0
        voting_list = []
        solo_won = []
        solo_lost = []
        team_won = []
        team_lost = []
        won_vote_names = []
        lost_vote_names = []
        draw_vote_names = []
        await ctx.send("Resetted votes.")

    if ctx.channel.id == twos_channel.id:
            
        draw_votes2 = 0
        won_votes2 = 0
        lost_votes2 = 0
        team_won2 = [] 
        team_lost2 = [] 
        won_vote_names2 = [] 
        lost_vote_names2 = []
        draw_vote_names2 = []
        await ctx.send("Resetted votes.")

    if ctx.channel.id == threes_channel.id:

        draw_votes3 = 0
        won_votes3 = 0
        lost_votes3 = 0
        team_won3 = []
        team_lost3 = []
        won_vote_names3 = []
        lost_vote_names3 = []
        draw_vote_names3 = []
        await ctx.send("Resetted votes.")

@client.command()
@commands.has_any_role('League Admin')
async def forcevote(ctx, vote, player: discord.Member):

    global draw_votes, won_votes, lost_votes, voting_list, solo_won, solo_lost, team_won, team_lost, won_vote_names, lost_vote_names, draw_vote_names, draw_votes2, won_votes2, lost_votes2, team_won2, team_lost2, won_vote_names2, lost_vote_names2, draw_vote_names2, draw_votes3, won_votes3, lost_votes3, team_won3, team_lost3, won_vote_names3, lost_vote_names3, draw_vote_names3

    if ctx.channel.id == threes_channel.id:

        activity_channel = ctx.guild.get_channel(790313358816968715)
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        auth = ctx.message.author.id

        c.execute("SELECT name FROM players_team WHERE ID = ?", [ctx.author.id])
        name = c.fetchone()[0]
        if name in no_score:
            no_score.remove(name)

        c.execute("SELECT currentg FROM players_team where ID = ?", [str(auth)])
        currentg = c.fetchone()
        currentgames = int(currentg[0])

        c.execute("SELECT * FROM games_team where ID = ?", [str(currentgames)])
        ids = c.fetchone()[1:7]

        if vote == "won":

            won_vote_names3.append(player.id)
            won_votes3 = won_votes3 + 1
            team_won.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (won). [{won_votes3}/3]")

        if vote == "lost":

            lost_vote_names3.append(player.id)
            lost_votes3 = lost_votes3 + 1
            team_lost3.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (lost). [{lost_votes3}/3]")

        if vote == "draw":

            draw_vote_names3.append(player.id)
            draw_votes3 = draw_votes3 + 1
            await ctx.send(f"Forcevoted {player.mention} (draw). [{draw_votes3}/3]")

        if won_votes3 == 3 and lost_votes3 == 3 and len(team_won3) == 3 and len(team_lost3) == 3:
        
            won_votes3 = 0
            lost_votes3 = 0 
            draw_votes3 = 0
            lost_vote_names3 = []
            won_vote_names3 = []
            draw_vote_names3 = []

            ELOS = []
            for t in ids:
                c.execute("SELECT elo FROM players_team where ID = ?", [str(t)])
                ELOS.append(c.fetchone()[0])

            team_1_ids = ELOS[0:3]
            team_2_ids = ELOS[3:6]

            team1 = sum(ELOS[0:3])
            team2 = sum(ELOS[3:6])

            skill = trueskill.rate_1vs1(trueskill.Rating(team1),trueskill.Rating(team2))
            team1n = skill[0].mu
            team2n = skill[1].mu    

            team1diff = np.ceil((team1n - team1)/4.0)
            team2diff = np.ceil((team2n - team2)/4.0)

            ELOS[0:3] = list(np.add(ELOS[0:3],team1diff))
            ELOS[3:6] = list(np.add(ELOS[3:6],team2diff))  

            diff = int(round(team1diff))

            min_elo_gain = 15

            if diff < min_elo_gain:
                diff = min_elo_gain

            if team1 > team2:
                diff = int(round(diff/2))

            if team2 > team1:
                diff = int(round(diff/2))

            await activity_channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
            await ctx.channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
           
            for t in ids:
                c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["win",currentgames])
                c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["lost",currentgames])
                c.execute("UPDATE games_team SET elodiff = ? WHERE ID = ?", [str(diff), currentgames])

            for t in team_won:
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in team_lost:  
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in team_won:
                c.execute("UPDATE players_team SET elo = elo + ? where ID = ?", [str(diff), str(t)])
                c.execute("UPDATE players_team SET win = win + 1 where ID = ?", [str(t)])
                c.execute("UPDATE players_team SET streak = streak + 1 WHERE ID = ?", [str(t)])

            for t in team_lost:
                c.execute("UPDATE players_team SET elo = elo - ? where ID = ?", [str(diff), str(t)])
                c.execute("UPDATE players_team SET loss = loss + 1 where ID = ?", [str(t)])
                c.execute("UPDATE players_team SET streak = 0 WHERE ID = ?", [str(t)])

            conn.commit()
            conn.close()

            await leaderboard_team(ctx)

        if draw_votes == 4:

            draw_votes = 0

            await activity_channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
            await ctx.channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")

            for t in ids:
                c.execute("UPDATE games_team SET elodiff = 0 WHERE ID = ?", [currentgames])

            for t in ids:
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in ids:
                c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["Draw",currentgames])
                c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["Draw",currentgames])

            conn.commit()
            conn.close()

    if ctx.channel.id == twos_channel.id:

        activity_channel = ctx.guild.get_channel(790313358816968715)
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        auth = ctx.message.author.id

        c.execute("SELECT name FROM players_team WHERE ID = ?", [ctx.author.id])
        name = c.fetchone()[0]

        if name in no_score:
            no_score.remove(name)

        c.execute("SELECT currentg FROM players_team where ID = ?", [str(auth)])
        currentg = c.fetchone()
        currentgames = int(currentg[0])

        c.execute("SELECT * FROM games_team where ID = ?", [str(currentgames)])
        ids = c.fetchone()[1:5]

        if vote == "won":
            won_vote_names2.append(player.id)
            won_votes2 = won_votes2 + 1
            team_won2.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (won). [{won_votes2}/2]")

        if vote == "lost":
            lost_vote_names2.append(player.id)
            lost_votes2 = lost_votes2 + 1
            team_lost2.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (lost). [{lost_votes2}/2]")

        if vote == "draw":
            draw_vote_names2.append(player.id)
            draw_votes2 = draw_votes2 + 1
            await ctx.send(f"Forcevoted {player.mention} (draw). [{draw_votes2}/2]")

        if won_votes2 == 2 and lost_votes2 == 2 and len(team_won2) == 2 and len(team_lost2) == 2:
        
            won_votes2 = 0
            lost_votes2 = 0 
            draw_votes2 = 0
            lost_vote_names2 = []
            won_vote_names2 = []
            draw_vote_names2 = []

            ELOS = []
            for t in ids:
                c.execute("SELECT elo FROM players_team where ID = ?", [str(t)])
                ELOS.append(c.fetchone()[0])

            team_1_ids = ELOS[0:2]
            team_2_ids = ELOS[2:4]

            team1 = sum(ELOS[0:2])
            team2 = sum(ELOS[2:4])

            skill = trueskill.rate_1vs1(trueskill.Rating(team1),trueskill.Rating(team2))
            team1n = skill[0].mu
            team2n = skill[1].mu    

            team1diff = np.ceil((team1n - team1)/4.0)
            team2diff = np.ceil((team2n - team2)/4.0)

            ELOS[0:2] = list(np.add(ELOS[0:2],team1diff))
            ELOS[2:4] = list(np.add(ELOS[2:4],team2diff))  

            diff = int(round(team1diff))

            min_elo_gain = 15

            if diff < min_elo_gain:
                diff = min_elo_gain

            if team1 > team2:
                diff = int(round(diff/2))

            if team2 > team1:
                diff = int(round(diff/2))

            await activity_channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
            await ctx.channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))

            for t in ids:
                c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["win",currentgames])
                c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["lost",currentgames])
                c.execute("UPDATE games_team SET elodiff = ? WHERE ID = ?", [str(diff), currentgames])

            for t in team_won2:
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in team_lost2:  
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in team_won2:
                c.execute("UPDATE players_team SET elo = elo + ? where ID = ?", [str(diff), str(t)])
                c.execute("UPDATE players_team SET win = win + 1 where ID = ?", [str(t)])
                c.execute("UPDATE players_team SET streak = streak + 1 WHERE ID = ?", [str(t)])

            for t in team_lost2:
                c.execute("UPDATE players_team SET elo = elo - ? where ID = ?", [str(diff), str(t)])
                c.execute("UPDATE players_team SET loss = loss + 1 where ID = ?", [str(t)])
                c.execute("UPDATE players_team SET streak = 0 WHERE ID = ?", [str(t)])

            team_won2 = []
            team_lost2 = []
            conn.commit()
            conn.close()

            await leaderboard_team(ctx)

        if draw_votes2 == 3:

            draw_votes2 = 0

            await activity_channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
            await ctx.channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")

            for t in ids:
                c.execute("UPDATE games_team SET elodiff = 0 WHERE ID = ?", [currentgames])

            for t in ids:
                c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

            for t in ids:
                c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["Draw",currentgames])
                c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["Draw",currentgames])

            conn.commit()
            conn.close()

    if ctx.channel.id == ones_channel.id:

        activity_channel = ctx.guild.get_channel(790313358816968715)
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        auth = ctx.message.author.id
        c.execute("SELECT name FROM players WHERE ID = ?", [ctx.author.id])
        name = c.fetchone()[0]
        if name in no_score:
            no_score.remove(name)
        c.execute("SELECT currentg FROM players where ID = ?", [str(auth)])
        currentg = c.fetchone()
        currentgames = int(currentg[0])

        c.execute("SELECT * FROM games where ID = ?", [str(currentgames)])
        ids = c.fetchone()[1:3]

        if vote == "won":
            won_vote_names.append(player.id)
            won_votes = won_votes + 1
            team_won.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (won). [{won_votes}/1]")

        if vote == "lost":
            lost_vote_names.append(player.id)
            lost_votes = lost_votes + 1
            team_lost.append(player.id)
            await ctx.send(f"Forcevoted {player.mention} (lost). [{lost_votes}/1]")

        if vote == "draw":
            draw_vote_names.append(player.id)
            draw_votes = draw_votes + 1
            await ctx.send(f"Forcevoted {player.mention} (draw). [{draw_votes}/2]")

        # if won_votes == 1 and lost_votes == 1 and len(team_won) == 1 and len(team_lost) == 1:
        
        #     won_votes = 0
        #     lost_votes = 0 
        #     draw_votes = 0
        #     lost_vote_names = []
        #     won_vote_names = []
        #     draw_vote_names = []
        #     ELOS = []

        #     for t in ids:
        #         c.execute("SELECT elo FROM players where ID = ?", [str(t)])
        #         ELOS.append(c.fetchone()[0])

        #     team_1_ids = ELOS[0:1]
        #     team_2_ids = ELOS[1:2]

        #     team1 = sum(ELOS[0:1])
        #     team2 = sum(ELOS[1:2])

        #     skill = trueskill.rate_1vs1(trueskill.Rating(team1),trueskill.Rating(team2))
        #     team1n = skill[0].mu
        #     team2n = skill[1].mu    

        #     team1diff = np.ceil((team1n - team1)/4.0)
        #     team2diff = np.ceil((team2n - team2)/4.0)

        #     ELOS[0:1] = list(np.add(ELOS[0:1],team1diff))
        #     ELOS[1:2] = list(np.add(ELOS[1:2],team2diff))  

        #     diff = int(round(team1diff))

        #     min_elo_gain = 15

        #     max_elo_gain = 200

        #     if diff < min_elo_gain:
        #         diff = min_elo_gain

        #     if team1 > team2:
        #         diff = int(round(diff/2))

        #     if team2 > team1:
        #         diff = int(round(diff/2))

        #     for t in team_won:
        #         c.execute("UPDATE players SET win = win + 1 where ID = ?", [str(t)])
        #         c.execute("UPDATE players SET streak = streak + 1 WHERE ID = ?", [str(t)])
        #         c.execute("UPDATE players SET elo = elo + ? where ID = ?", [str(diff), t])

        #     for t in team_lost:
        #         c.execute("UPDATE players SET loss = loss + 1 where ID = ?", [str(t)])
        #         c.execute("UPDATE players SET streak = 0 WHERE ID = ?", [str(t)])
        #         c.execute("UPDATE players SET elo = elo - ? where ID = ?", [str(diff), t])

        #     for t in ids:
        #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["win",currentgames])
        #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["lost",currentgames])
        #         c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])
        #         c.execute("UPDATE games SET elodiff = ? WHERE ID = ?", [str(diff), currentgames])

        #     team_won = []
        #     team_lost = []
        #     conn.commit()
        #     conn.close()

        #     await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
        #     await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
        #     await leaderboard_solo(ctx)


        # if draw_votes == 2:

        #     draw_votes = 0

        #     await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
        #     await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
   
        #     for t in ids:
        #         c.execute("UPDATE games SET elodiff = 0 WHERE ID = ?", [currentgames])

        #     for t in ids:
        #         c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(t)])

        #     for t in ids:
        #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["Draw",currentgames])
        #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["Draw",currentgames])

        #     conn.commit()
        #     conn.close()

@client.command()
@commands.cooldown(1, 1, commands.BucketType.user)
async def game(ctx, result):
    """Process game results."""

    if ctx.channel.id == threes_channel.id or ctx.channel.id == twos_channel.id:

        if result not in ["won", "lost", "draw"]:
            await ctx.send("Invalid vote.")
            return
        
        activity_channel = ctx.guild.get_channel(790313358816968715)
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        auth = ctx.message.author.id

        c.execute("SELECT name FROM players_team WHERE ID = ?", [ctx.author.id])
        name = c.fetchone()[0]
        if name in no_score:
            no_score.remove(name)

        c.execute("SELECT currentg FROM players_team where ID = ?", [str(auth)])
        currentg = c.fetchone()
        game_id = int(currentg[0])

        game_dict = global_dict[game_id]
        ids = game_dict["ids"]
        num_players = len(ids)
        players_per_team = int(len(ids)/2)
        team_index = game_dict["player_to_team"][auth]
        old_vote = game_dict["player_votes"][auth] # empty str "" means no vote

        game_type = f"{players_per_team}v{players_per_team}"

        await ctx.send(f"[{game_type}] Game #{game_id}: <@{auth}> voted {result}.")

        if old_vote != result:

            if old_vote != "":
                game_dict[old_vote][team_index] -= 1
                game_dict[old_vote][2] -= 1
            else:
                game_dict["vote_count"] += 1

            game_dict["player_votes"][auth] = result
            game_dict[result][team_index] += 1
            game_dict[result][2] += 1

            if game_dict["draw"][2] >= players_per_team + 1:
                await activity_channel.send(f"[{game_type}] Game #" + str(game_id) + " has been drawn.")
                await ctx.channel.send(f"[{game_type}] Game #" + str(game_id) + " has been drawn.")

                for t in ids:
                    c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])

                c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["Draw", game_id])
                c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["Draw", game_id])

                conn.commit()
                conn.close()
                del global_dict[game_id]

            elif game_dict["vote_count"] == num_players:
                if game_dict["won"][2] != players_per_team or game_dict["lost"][2] != players_per_team or not (game_dict["won"][0] == players_per_team or game_dict["won"][1] == players_per_team):
                    await ctx.send("One team must win and the other must lose - All players on each team must vote correctly. Votes have been reset.")
                    game_dict["player_votes"] = defaultdict(str)
                    game_dict["vote_count"] = 0
                    game_dict["won"] = [0, 0, 0]
                    game_dict["lost"] = [0, 0, 0]
                    game_dict["draw"] = [0, 0, 0]
                else:
                    team_won = game_dict["teams"][0]
                    team_lost = game_dict["teams"][1]

                    if game_dict["won"][0] != players_per_team:
                        team_won, team_lost = team_lost, team_won
                        c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["lost",game_id])
                        c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["won",game_id])
                    else:
                        c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["won",game_id])
                        c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["lost",game_id])
                
                    ELOS = []
                    
                    team1 = []
                    for t in team_won:
                        c.execute("SELECT elo, sigma FROM players_team where ID = ?", [str(t)])
                        row = c.fetchone()
                        elo = row[0]
                        sigma = row[1]
                        team1.append(trueskill.Rating(elo, sigma))
                    
                    team2 = []
                    for t in team_lost:
                        c.execute("SELECT elo, sigma FROM players_team where ID = ?", [str(t)])
                        row = c.fetchone()
                        elo = row[0]
                        sigma = row[1]
                        team2.append(trueskill.Rating(elo, sigma))

                    team1, team2 = trueskill.rate([team1, team2])

                    for i, t in enumerate(team_won):
                        c.execute("UPDATE players_team SET win = win + 1 where ID = ?", [str(t)])
                        c.execute("UPDATE players_team SET streak = streak + 1 WHERE ID = ?", [str(t)])
                        c.execute("UPDATE players_team SET elo = ? where ID = ?", [team1[i].mu, t])
                        c.execute("UPDATE players_team SET sigma = ? where ID = ?", [team1[i].sigma, t])
                        c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [t])

                    for i, t in enumerate(team_lost):
                        c.execute("UPDATE players_team SET loss = loss + 1 where ID = ?", [str(t)])
                        c.execute("UPDATE players_team SET streak = 0 WHERE ID = ?", [str(t)])
                        c.execute("UPDATE players_team SET elo = ? where ID = ?", [team2[i].mu, t])
                        c.execute("UPDATE players_team SET sigma = ? where ID = ?", [team2[i].sigma, t])
                        c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [t])

                    conn.commit()
                    conn.close()
                    del global_dict[game_id]

                    await activity_channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")
                    await ctx.channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")                    
                    await leaderboard_team(ctx)

    if ctx.channel.id == ones_channel.id:
        
        if result not in ["won", "lost", "draw"]:
            await ctx.send("Invalid vote.")
            return

        activity_channel = ctx.guild.get_channel(790313358816968715)
        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()
        auth = ctx.message.author.id
        c.execute("SELECT name FROM players WHERE ID = ?", [ctx.author.id])
        name = c.fetchone()[0]
        if name in no_score:
            no_score.remove(name)
        c.execute("SELECT currentg FROM players where ID = ?", [str(auth)])
        currentg = c.fetchone()
        game_id = int(currentg[0])

        # c.execute("SELECT * FROM games where ID = ?", [str(game_id)])
        # ids = c.fetchone()[1:3]
        game_dict = global_dict[game_id]
        ids = game_dict["ids"]
        num_players = len(ids)
        players_per_team = len(ids)/2
        team_index = game_dict["player_to_team"][auth]
        old_vote = game_dict["player_votes"][auth] # empty str "" means no vote

        await ctx.send(f"[1v1] Game #{game_id}: <@{auth}> voted {result}.")

        if auth == ids[0] or auth == ids[1] and num_players == 2 and old_vote != result:
            
            if old_vote != "":
                game_dict[old_vote][team_index] -= 1
                game_dict[old_vote][2] -= 1
            else:
                game_dict["vote_count"] += 1

            game_dict["player_votes"][auth] = result
            game_dict[result][team_index] += 1
            game_dict[result][2] += 1

            if game_dict["vote_count"] == num_players:
                if game_dict["draw"][2] == num_players:
                    await activity_channel.send("[1v1] Game #" + str(game_id) + " has been drawn.")
                    await ctx.channel.send("[1v1] Game #" + str(game_id) + " has been drawn.")

                    for t in ids:
                        c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(t)])

                    c.execute("UPDATE games SET s1 = ? where ID = ?", ["Draw",game_id])
                    c.execute("UPDATE games SET s2 = ? where ID = ?", ["Draw",game_id])

                    conn.commit()
                    conn.close()
                    del global_dict[game_id]

                elif game_dict["won"][2] != players_per_team or game_dict["lost"][2] != players_per_team or not (game_dict["won"][0] == players_per_team or game_dict["won"][1] == players_per_team):
                    await ctx.send("One team must win and the other must lose - All players on each team must vote correctly. Votes have been reset.")
                    game_dict["player_votes"] = defaultdict(str)
                    game_dict["vote_count"] = 0
                    game_dict["won"] = [0, 0, 0]
                    game_dict["lost"] = [0, 0, 0]
                    game_dict["draw"] = [0, 0, 0]
                else:
                    team_won = game_dict["teams"][0]
                    team_lost = game_dict["teams"][1]

                    if game_dict["won"][0] != players_per_team:
                        team_won, team_lost = team_lost, team_won
                        c.execute("UPDATE games SET s1 = ? where ID = ?", ["lost",game_id])
                        c.execute("UPDATE games SET s2 = ? where ID = ?", ["won",game_id])
                    else:
                        c.execute("UPDATE games SET s1 = ? where ID = ?", ["won",game_id])
                        c.execute("UPDATE games SET s2 = ? where ID = ?", ["lost",game_id])

                    # ELOS = []
                    for t in team_won:
                        c.execute("SELECT elo, sigma FROM players where ID = ?", [str(t)])
                        row1 = c.fetchone()
                        elo1 = row1[0]
                        sigma1 = row1[1]
                        # ELOS.append(c.fetchone())
                    
                    for t in team_lost:
                        c.execute("SELECT elo, sigma FROM players where ID = ?", [str(t)])
                        row2 = c.fetchone()
                        elo2 = row2[0]
                        sigma2 = row2[1]
                        # ELOS.append(c.fetchone())

                    skill = trueskill.rate_1vs1(trueskill.Rating(elo1, sigma1),trueskill.Rating(elo2, sigma2))

                    for t in team_won:
                        c.execute("UPDATE players SET win = win + 1 where ID = ?", [str(t)])
                        c.execute("UPDATE players SET streak = streak + 1 WHERE ID = ?", [str(t)])
                        c.execute("UPDATE players SET elo = ? where ID = ?", [skill[0].mu, t])
                        c.execute("UPDATE players SET sigma = ? where ID = ?", [skill[0].sigma, t])
                        c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])

                    for t in team_lost:
                        c.execute("UPDATE players SET loss = loss + 1 where ID = ?", [str(t)])
                        c.execute("UPDATE players SET streak = 0 WHERE ID = ?", [str(t)])
                        c.execute("UPDATE players SET elo = ? where ID = ?", [skill[1].mu, t])
                        c.execute("UPDATE players SET sigma = ? where ID = ?", [skill[1].sigma, t])
                        c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])

                    conn.commit()
                    conn.close()
                    del global_dict[game_id]

                    await activity_channel.send("[1v1] Game #" + str(game_id) + " has finished.")
                    await ctx.channel.send("[1v1] Game #" + str(game_id) + " has finished.")
                    await leaderboard_solo(ctx)

        # global ones_votes

        # activity_channel = ctx.guild.get_channel(784960784056582174)
        # conn = sqlite3.connect(db_path, uri=True)
        # c = conn.cursor()
        # auth = ctx.message.author.id
        # c.execute("SELECT name FROM players WHERE ID = ?", [ctx.author.id])
        # name = c.fetchone()[0]
        # if name in no_score:
        #     no_score.remove(name)
        # c.execute("SELECT currentg FROM players where ID = ?", [str(auth)])
        # currentg = c.fetchone()
        # currentgames = int(currentg[0])

        # if not ones_votes.get(currentgames):
        #     ones_votes[currentgames] = dict()

        # ones_votes[currentgames][str(auth)] = result
        # print(ones_votes)

        # size = len(list(ones_votes[currentgames]))

        # c.execute("SELECT * FROM games where ID = ?", [str(currentgames)])
        # ids = c.fetchone()[1:3]

        # if auth == ids[0] or auth == ids[1] and len(ids) == 2:

        #     if result == "draw":
        #         draw_votes = draw_votes + 1
        #         await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted draw.")

        #     if result == "won":
        #         won_votes = won_votes + 1
        #         solo_won = auth
        #         team_won.append(auth)
        #         await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted winner.")

        #     if result == "lost":
        #         lost_votes = lost_votes + 1
        #         solo_lost = auth
        #         team_lost.append(auth)
        #         await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted loser.")

        #     if won_votes == 2:
        #         won_votes = 0
        #         await ctx.send("Incorrect number of votes.")
            
        #     if lost_votes == 2:
        #         lost_votes = 0
        #         await ctx.send("Incorrect number of votes.")

        #     if won_votes == 1 and lost_votes == 1 and team_won != team_lost:

        #         won_votes = 0
        #         lost_votes = 0

        #         ELOS = []
        #         for t in team_won:
        #             c.execute("SELECT elo, sigma FROM players where ID = ?", [str(t)])
        #             row = c.fetchone()
        #             elo1 = row[0]
        #             sigma1 = row[1]
        #             ELOS.append(c.fetchone())
                
        #         for t in team_lost:
        #             c.execute("SELECT elo, sigma FROM players where ID = ?", [str(t)])
        #             row2 = c.fetchone()
        #             elo2 = row2[0]
        #             sigma2 = row2[1]
        #             ELOS.append(c.fetchone())

        #         skill = trueskill.rate_1vs1(trueskill.Rating(elo1, sigma1),trueskill.Rating(elo2, sigma2))

        #         for t in team_won:
        #             c.execute("UPDATE players SET win = win + 1 where ID = ?", [str(t)])
        #             c.execute("UPDATE players SET streak = streak + 1 WHERE ID = ?", [str(t)])
        #             c.execute("UPDATE players SET elo = ? where ID = ?", [skill[0].mu, t])
        #             c.execute("UPDATE players SET sigma = ? where ID = ?", [skill[0].sigma, t])
        #             c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])

        #         for t in team_lost:
        #             c.execute("UPDATE players SET loss = loss + 1 where ID = ?", [str(t)])
        #             c.execute("UPDATE players SET streak = 0 WHERE ID = ?", [str(t)])
        #             c.execute("UPDATE players SET elo = ? where ID = ?", [skill[1].mu, t])
        #             c.execute("UPDATE players SET sigma = ? where ID = ?", [skill[1].sigma, t])
        #             c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])

        #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["win",currentgames])
        #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["lost",currentgames])

        #         team_won = []
        #         team_lost = []
        #         conn.commit()
        #         conn.close()

        #         await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished.")
        #         await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished.")
        #         await leaderboard_solo(ctx)

        #     if draw_votes == 2:

        #         draw_votes = 0

        #         await activity_channel.send("[1v1] Game #" + str(currentgames) + " has been drawn.")
        #         await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has been drawn.")

        #         for t in ids:
        #             c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(t)])

        #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["Draw",currentgames])
        #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["Draw",currentgames])

        #         conn.commit()
        #         conn.close()

###########################################################################################################
            #     ELOS = []
            #     for t in ids:
            #         c.execute("SELECT elo FROM players where ID = ?", [str(t)])
            #         ELOS.append(c.fetchone()[0])

            #     #team1sigma = 
            #     #team2sigma =
                    
            #     team1 = sum(ELOS[0:1])
            #     team2 = sum(ELOS[1:2])

            #     skill = trueskill.rate_1vs1(trueskill.Rating(team1,team1sigma),trueskill.Rating(team2,team2sigma))
            #     team1n = skill[0].mu
            #     team2n = skill[1].mu    

            #     team1diff = np.ceil((team1n - team1)/4.0)
            #     team2diff = np.ceil((team2n - team2)/4.0)

            #     ELOS[0:1] = list(np.add(ELOS[0:1],team1diff))
            #     ELOS[1:2] = list(np.add(ELOS[1:2],team2diff))  

            #     diff = int(round(team1diff))

            #     min_elo_gain = 15

            #     #max_elo_gain = 200

            #     if diff < min_elo_gain:
            #         diff = min_elo_gain

            #     if team1 > team2:
            #         diff = int(round(diff/2))

            #     if team2 > team1:
            #         diff = int(round(diff/2))

            #     print(team_won)
            #     print(team_lost)

            #     for t in team_won:
            #         c.execute("UPDATE players SET win = win + 1 where ID = ?", [str(t)])
            #         c.execute("UPDATE players SET streak = streak + 1 WHERE ID = ?", [str(t)])
            #         c.execute("UPDATE players SET elo = elo + ? where ID = ?", [str(diff), t])

            #     for t in team_lost:
            #         c.execute("UPDATE players SET loss = loss + 1 where ID = ?", [str(t)])
            #         c.execute("UPDATE players SET streak = 0 WHERE ID = ?", [str(t)])
            #         c.execute("UPDATE players SET elo = elo - ? where ID = ?", [str(diff), t])

            #     for t in ids:
            #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["win",currentgames])
            #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["lost",currentgames])
            #         c.execute("UPDATE players SET currentg = NULL where ID = ?", [t])
            #         c.execute("UPDATE games SET elodiff = ? WHERE ID = ?", [str(diff), currentgames])

            #     team_won = []
            #     team_lost = []
            #     conn.commit()
            #     conn.close()

            #     await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
            #     await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
            #     await leaderboard_solo(ctx)

            # if draw_votes == 2:

            #     draw_votes = 0

            #     await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
            #     await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    
            #     for t in ids:
            #         c.execute("UPDATE games SET elodiff = 0 WHERE ID = ?", [currentgames])

            #     for t in ids:
            #         c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(t)])

            #     for t in ids:
            #         c.execute("UPDATE games SET s1 = ? where ID = ?", ["Draw",currentgames])
            #         c.execute("UPDATE games SET s2 = ? where ID = ?", ["Draw",currentgames])

            #     conn.commit()
            #     conn.close()

    # if ctx.channel.id == ones_channel.id:
  
    #     activity_channel = ctx.guild.get_channel(784960784056582174)
    #     conn = sqlite3.connect(db_path, uri=True)
    #     c = conn.cursor()
    #     auth = ctx.message.author.id
    #     c.execute("SELECT name FROM players WHERE ID = ?", [ctx.author.id])
    #     name = c.fetchone()[0]
    #     if name in no_score:
    #         no_score.remove(name)
    #     c.execute("SELECT currentg FROM players where ID = ?", [str(auth)])
    #     currentg = c.fetchone()
    #     if currentg[0] == None:
    #         await ctx.send("You're not in a game.")
    #         return
    #     currentgames = int(currentg[0])

    #     c.execute("SELECT * FROM games where ID = ?", [str(currentgames)])
    #     ids = c.fetchone()[1:3]

    #     if auth == ids[0] or auth == ids[1] and len(ids) == 2:

    #         if result == "draw":
    #             draw_votes = draw_votes + 1
    #             await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted draw.")

    #         if result == "won":
    #             won_votes = won_votes + 1
    #             solo_won = auth
    #             await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted winner.")

    #         if result == "lost":
    #             lost_votes = lost_votes + 1
    #             solo_lost = auth
    #             await ctx.send(f"[1v1] Game #{currentgames}: <@{auth}> voted loser.")

    #         if won_votes == 2:
    #             won_votes = 0
            
    #         if lost_votes == 2:
    #             lost_votes = 0

    #         if won_votes == 1 and lost_votes == 1:
    #             won_votes = 0
    #             lost_votes = 0 

    #             ELOS = []
    #             for t in ids:
    #                 c.execute("SELECT elo FROM players where ID = ?", [str(t)])
    #                 ELOS.append(c.fetchone()[0])

    #             team1 = sum(ELOS[0:1])
    #             team2 = sum(ELOS[1:2])
    #             team1diff = np.ceil(team1/2)
    #             team2diff = np.ceil(team2/2)            

    #             diff = np.abs(team1diff - team2diff)

    #             min_elo_gain = 10
    #             if diff < min_elo_gain:
    #                 diff = min_elo_gain

    #             max_elo_gain = 120

    #             if diff > max_elo_gain:
    #                 diff = max_elo_gain
    #             if team1diff > team2diff:
    #                 diff = diff/2
    #                 rounded_diff = round(diff)
    #             else:
    #                 diff = diff
    #                 rounded_diff = round(diff)
    #             await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             for t in ids:
    #                 c.execute("UPDATE games SET s1 = ? where ID = ?", ["win",currentgames])
    #                 c.execute("UPDATE games SET s2 = ? where ID = ?", ["lost",currentgames])
    #                 c.execute("UPDATE games SET elodiff = ? WHERE ID = ?", [str(rounded_diff), currentgames])
    #                 c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(solo_won)])
    #                 c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(solo_lost)])
    #             for t in ids:
    #                 c.execute("UPDATE players SET elo = elo + ? where ID = ?", [str(rounded_diff), str(solo_won)])
    #                 c.execute("UPDATE players SET elo = elo - ? where ID = ?", [str(rounded_diff), str(solo_lost)])
    #                 c.execute("UPDATE players SET win = win + 1 where ID = ?", [str(solo_won)])
    #                 c.execute("UPDATE players SET loss = loss + 1 where ID = ?", [str(solo_lost)])
    #                 c.execute("UPDATE players SET streak = 0 WHERE ID = ?", [str(solo_lost)])
    #                 c.execute("UPDATE players SET streak = streak + 1 WHERE ID = ?", [str(solo_won)])
    #             conn.commit()
    #             conn.close()
    #             await leaderboard_solo(ctx)

    #         if draw_votes == 2:
    #             draw_votes = 0
    #             await activity_channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             await ctx.channel.send("[1v1] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             for t in ids:
    #                 c.execute("UPDATE games SET elodiff = 0 WHERE ID = ?", [currentgames])
    #             for t in ids:
    #                 c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(solo_won)])
    #                 c.execute("UPDATE players SET currentg = NULL where ID = ?", [str(solo_lost)])
    #             for t in ids:
    #                 c.execute("UPDATE games SET s1 = ? where ID = ?", ["Draw",currentgames])
    #                 c.execute("UPDATE games SET s2 = ? where ID = ?", ["Draw",currentgames])
    #             conn.commit()
    #             conn.close()

    # if ctx.channel.id == twos_channel.id:

    #     activity_channel = ctx.guild.get_channel(784960784056582174)
    #     conn = sqlite3.connect(db_path, uri=True)
    #     c = conn.cursor()
    #     auth = ctx.message.author.id
    #     c.execute("SELECT name FROM players_team WHERE ID = ?", [ctx.author.id])
    #     name = c.fetchone()[0]
    #     if name in no_score:
    #         no_score.remove(name)
    #     c.execute("SELECT currentg FROM players_team where ID = ?", [str(auth)])
    #     currentg = c.fetchone()
    #     if currentg[0] == None:
    #         await ctx.send("You're not in a game.")
    #         return
    #     currentgames = int(currentg[0])

    #     c.execute("SELECT * FROM games_team where ID = ?", [str(currentgames)])
    #     ids = c.fetchone()[1:5]

    #     if auth == ids[0] or auth == ids[1] or auth == ids[2] or auth == ids[3] or auth == ids[4] or auth == ids[5] and len(ids) == 4:

    #         if auth in lost_vote_names2 or auth in won_vote_names2 or auth in lost_vote_names2:
    #             await ctx.send(f"<@{auth}>, you have already voted!")
    #             return

    #         if result == "draw" and auth not in draw_vote_names2:
    #             draw_vote_names2.append(auth)
    #             draw_votes2 = draw_votes2 + 1
    #             await ctx.send(f"[2v2] Game #{currentgames}: <@{auth}> voted draw. [{draw_votes2}/2]")

    #         if result == "won" and auth not in won_vote_names2:
    #             won_vote_names2.append(auth)
    #             won_votes2 = won_votes2 + 1
    #             team_won2.append(auth)
    #             await ctx.send(f"[2v2] Game #{currentgames}: <@{auth}> voted winner. [{won_votes2}/2]")

    #         if result == "lost" and auth not in lost_vote_names2:
    #             lost_vote_names2.append(auth)
    #             lost_votes2 = lost_votes2 + 1
    #             team_lost2.append(auth)
    #             await ctx.send(f"[2v2] Game #{currentgames}: <@{auth}> voted loser. [{lost_votes2}/2]")
            
    #         if won_votes2 > 2:
    #             won_votes2 = 0
            
    #         if lost_votes2 > 2:
    #             lost_votes2 = 0

    #         if won_votes2 == 2 and lost_votes2 == 2 and len(team_won2) == 2 and len(team_lost2) == 2:
    #             won_votes2 = 0
    #             lost_votes2 = 0 
    #             draw_votes2 = 0
    #             lost_vote_names2 = []
    #             won_vote_names2 = []
    #             draw_vote_names2 = []

    #             ELOS = []
    #             for t in ids:
    #                 c.execute("SELECT elo FROM players_team where ID = ?", [str(t)])
    #                 ELOS.append(c.fetchone()[0])

    #             team_1_ids2 = ELOS[0:2]
    #             team_2_ids2 = ELOS[2:4]

    #             team1 = sum(ELOS[0:2])
    #             team2 = sum(ELOS[2:4])
    #             team1diff = np.ceil(team1/3)
    #             team2diff = np.ceil(team2/3)       

    #             diff = np.abs(team1diff - team2diff)

    #             min_elo_gain = 10
    #             if diff < min_elo_gain:
    #                 diff = min_elo_gain

    #             max_elo_gain = 120

    #             if diff > max_elo_gain:
    #                 diff = max_elo_gain
    #             if team1diff > team2diff:
    #                 diff = diff/2
    #                 rounded_diff = round(diff)
    #             else:
    #                 diff = diff
    #                 rounded_diff = round(diff)
    #             await activity_channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             await ctx.channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["win",currentgames])
    #                 c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["lost",currentgames])
    #                 c.execute("UPDATE games_team SET elodiff = ? WHERE ID = ?", [str(rounded_diff), currentgames])
    #             for t in team_won2:
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in team_lost2:  
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in team_won2:
    #                 c.execute("UPDATE players_team SET elo = elo + ? where ID = ?", [str(rounded_diff), str(t)])
    #                 c.execute("UPDATE players_team SET win = win + 1 where ID = ?", [str(t)])
    #                 c.execute("UPDATE players_team SET streak = streak + 1 WHERE ID = ?", [str(t)])
    #             for t in team_lost2:
    #                 c.execute("UPDATE players_team SET elo = elo - ? where ID = ?", [str(rounded_diff), str(t)])
    #                 c.execute("UPDATE players_team SET loss = loss + 1 where ID = ?", [str(t)])
    #                 c.execute("UPDATE players_team SET streak = 0 WHERE ID = ?", [str(t)])

    #             team_won2 = []
    #             team_lost2 = []
    #             conn.commit()
    #             conn.close()
    #             await leaderboard_team(ctx)

    #         if draw_votes == 3:
    #             draw_votes = 0
    #             await activity_channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             await ctx.channel.send("[2v2] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET elodiff = 0 WHERE ID = ?", [currentgames])
    #             for t in ids:
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["Draw",currentgames])
    #                 c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["Draw",currentgames])
    #             conn.commit()
    #             conn.close()


    # if ctx.channel.id == threes_channel.id:

    #     activity_channel = ctx.guild.get_channel(784960784056582174)
    #     conn = sqlite3.connect(db_path, uri=True)
    #     c = conn.cursor()
    #     auth = ctx.message.author.id
    #     c.execute("SELECT name FROM players_team WHERE ID = ?", [ctx.author.id])
    #     name = c.fetchone()[0]
    #     if name in no_score:
    #         no_score.remove(name)
    #     c.execute("SELECT currentg FROM players_team where ID = ?", [str(auth)])
    #     currentg = c.fetchone()
    #     if currentg[0] == None:
    #         await ctx.send("You're not in a game.")
    #         return
    #     currentgames = int(currentg[0])

    #     c.execute("SELECT * FROM games_team where ID = ?", [str(currentgames)])
    #     ids = c.fetchone()[1:7]

    #     if auth == ids[0] or auth == ids[1] or auth == ids[2] or auth == ids[3] or auth == ids[4] or auth == ids[5] and len(ids) == 6:

    #         if auth in lost_vote_names3 or auth in won_vote_names3 or auth in lost_vote_names3:
    #             await ctx.send(f"<@{auth}>, you have already voted!")
    #             return

    #         if result == "draw" and auth not in draw_vote_names3:
    #             draw_vote_names3.append(auth)
    #             draw_votes3 = draw_votes3 + 1
    #             await ctx.send(f"[3v3] Game #{currentgames}: <@{auth}> voted draw. [{draw_votes3}/3]")

    #         if result == "won" and auth not in won_vote_names3:
    #             won_vote_names3.append(auth)
    #             won_votes3 = won_votes3 + 1
    #             team_won.append(auth)
    #             await ctx.send(f"[3v3] Game #{currentgames}: <@{auth}> voted winner. [{won_votes3}/3]")

    #         if result == "lost" and auth not in lost_vote_names3:
    #             lost_vote_names3.append(auth)
    #             lost_votes3 = lost_votes3 + 1
    #             team_lost3.append(auth)
    #             await ctx.send(f"[3v3] Game #{currentgames}: <@{auth}> voted loser. [{lost_votes3}/3]")
            
    #         if won_votes3 > 3:
    #             won_votes3 = 0
            
    #         if lost_votes3 > 3:
    #             lost_votes3 = 0

    #         if won_votes3 == 3 and lost_votes3 == 3 and len(team_won3) == 3 and len(team_lost3) == 3:
    #             won_votes3 = 0
    #             lost_votes3 = 0 
    #             draw_votes3 = 0
    #             lost_vote_names3 = []
    #             won_vote_names3 = []
    #             draw_vote_names3 = []

    #             ELOS = []
    #             for t in ids:
    #                 c.execute("SELECT elo FROM players_team where ID = ?", [str(t)])
    #                 ELOS.append(c.fetchone()[0])

    #             team_1_ids3 = ELOS[0:3]
    #             team_2_ids3 = ELOS[3:6]

    #             team1 = sum(ELOS[0:3])
    #             team2 = sum(ELOS[3:6])
    #             team1diff = np.ceil(team1/3)
    #             team2diff = np.ceil(team2/3)       

    #             diff = np.abs(team1diff - team2diff)

    #             min_elo_gain = 10
    #             if diff < min_elo_gain:
    #                 diff = min_elo_gain

    #             max_elo_gain = 120

    #             if diff > max_elo_gain:
    #                 diff = max_elo_gain
    #             if team1diff > team2diff:
    #                 diff = diff/2
    #                 rounded_diff = round(diff)
    #             else:
    #                 diff = diff
    #                 rounded_diff = round(diff)
    #             await activity_channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             await ctx.channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- " + str(diff))
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["win",currentgames])
    #                 c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["lost",currentgames])
    #                 c.execute("UPDATE games_team SET elodiff = ? WHERE ID = ?", [str(rounded_diff), currentgames])
    #             for t in team_won3:
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in team_lost3:  
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in team_won3:
    #                 c.execute("UPDATE players_team SET elo = elo + ? where ID = ?", [str(rounded_diff), str(t)])
    #                 c.execute("UPDATE players_team SET win = win + 1 where ID = ?", [str(t)])
    #                 c.execute("UPDATE players_team SET streak = streak + 1 WHERE ID = ?", [str(t)])
    #             for t in team_lost3:
    #                 c.execute("UPDATE players_team SET elo = elo - ? where ID = ?", [str(rounded_diff), str(t)])
    #                 c.execute("UPDATE players_team SET loss = loss + 1 where ID = ?", [str(t)])
    #                 c.execute("UPDATE players_team SET streak = 0 WHERE ID = ?", [str(t)])

    #             team_won3 = []
    #             team_lost3 = []
    #             conn.commit()
    #             conn.close()
    #             await leaderboard_team(ctx)

    #         if draw_votes3 == 4:
    #             draw_votes3 = 0
    #             await activity_channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             await ctx.channel.send("[3v3] Game #" + str(currentgames) + " has finished with ELO Difference of +/- 0")
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET elodiff = 0 WHERE ID = ?", [currentgames])
    #             for t in ids:
    #                 c.execute("UPDATE players_team SET currentg = NULL where ID = ?", [str(t)])
    #             for t in ids:
    #                 c.execute("UPDATE games_team SET s1 = ? where ID = ?", ["Draw",currentgames])
    #                 c.execute("UPDATE games_team SET s2 = ? where ID = ?", ["Draw",currentgames])
    #             conn.commit()
    #             conn.close()

@client.command()
async def stats(ctx):
    '''Shows a players statistics.'''

    global PLAYERS, PLAYERS2, PLAYERS3, db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
            
        name = str(ctx.message.content)[7:]
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        conn = sqlite3.connect(db_path, uri=True)

        c = conn.cursor()
        c.execute("SELECT name, elo, win, loss, streak, profile, fresh_warns, record, perms, rank, sigma FROM players where ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            name = player[0]
            pts = int(round(player[1]))
            win = player[2]
            loss = player[3]
            streak = player[4]
            url = player[5]
            warns = player[6]
            peak = player[7]
            description = player[8]
            rank = player[9]
            sigma = int(round(player[10]))
            total_games = win + loss
            if streak > 0:
                streak = f"{streak}"
            if total_games == 0:
                # embed = discord.Embed(
                #     colour=0x1F1E1E
                # )
                # embed.set_thumbnail(url=url)
                # embed.add_field(name=f"{name}\n\u200b",
                #                 value=f'**{name}** has played no games and has an elo of **{pts}**.', inline=False)
                # await ctx.send(embed=embed)
                await ctx.channel.send(name + " played no games and has an elo of **" + str(pts) + "**.")
            else:
                winrate = float("{0:.2f}".format((win / total_games) * 100))
                # await ctx.channel.send(name + "(" + str(pts) + ") has " + str(total_games) + " games played, " + str(win) + " wins, " + str(loss) + " losses.\nWinrate: " + str(winrate) + "%\nStreak: 0.")
                await ctx.channel.send("**" + name + "** has played **" + str(total_games) + "** games with a win rate of **" + str(winrate) + "%** (**" + str(win) + "**W - **" + str(loss) + "**L). Their ELO: **" + str(pts) + "**. Sigma: **" + str(sigma) + "**. Streak: **" + str(streak) + "**. Rank: **" + str(rank) + "**.")
                # embed = discord.Embed(
                #     colour = 0x1F1E1E
                # )
                # embed.add_field(name="Statistics\n\u200b", value=f'**{name}** has played a total of **{total_games}** games with a win rate of **{winrate}**%\nCurrent win streak: **{winstreak}**; Current loss streak: **{loss_streak}**; Warnings: **{warns}**', inline=False)
                # embed.add_field(name='\n\u200b', value=f'ELO: **{pts}**')
                # embed.add_field(name='\n\u200b', value=f'Wins: **{win}**')
                # embed.add_field(name='\n\u200b', value=f'Losses: **{loss}**')

                # await ctx.channel.send(embed=embed)
                # embed = discord.Embed(
                #     colour=0x1F1E1E
                # )
                # embed.set_thumbnail(url=url)
                # embed.add_field(name=f"{name}\n\u200b",
                #                 value=f'**{name}** has played a total of **{total_games}** games with a win rate of **{winrate}**%',
                #                 inline=False)
                # embed.add_field(name='\n\u200b', value=f'ELO: **{pts}**')
                # embed.add_field(name='\n\u200b', value=f'Wins: **{win}**')
                # embed.add_field(name='\n\u200b', value=f'Losses: **{loss}**')
                # embed.add_field(name='\n\u200b', value=f'Streak: **{streak}**')
                # embed.add_field(name='\n\u200b', value=f'Warnings: **{warns}**/**4**')
                # embed.add_field(name='\n\u200b', value=f'Peak: **{peak}**\n')
                # embed.add_field(name='\n\u200b', value=f"**Additional Information**\n\n{description}")
                # embed.set_footer(text="\n\u200bTip: You can change your profile picture by typing !profile add link.")
                # embed.set_footer(text="Tip: [You can change your picture by typing !profile add (link)](https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg")
                # await ctx.send(embed=embed)
        else:
            await ctx.channel.send("No user found by that name!")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()
            
        name = str(ctx.message.content)[7:]
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        conn = sqlite3.connect(db_path, uri=True)

        c = conn.cursor()
        c.execute("SELECT name, elo, win, loss, streak, profile, fresh_warns, record, perms, rank, sigma FROM players_team where ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            name = player[0]
            pts = int(round(player[1]))
            win = player[2]
            loss = player[3]
            streak = player[4]
            url = player[5]
            warns = player[6]
            peak = player[7]
            description = player[8]
            rank = player[9]
            sigma = int(round(player[10]))
            total_games = win + loss
            if streak > 0:
                streak = f"{streak}"
            if total_games == 0:
                # embed = discord.Embed(
                #     colour=0x1F1E1E
                # )
                # embed.set_thumbnail(url=url)
                # embed.add_field(name=f"{name}\n\u200b",
                #                 value=f'**{name}** has played no games and has an elo of **{pts}**.', inline=False)
                # await ctx.send(embed=embed)
                await ctx.channel.send(name + " played no games and has an elo of **" + str(pts) + "**.")
            else:
                winrate = float("{0:.2f}".format((win / total_games) * 100))
                # await ctx.channel.send(name + "(" + str(pts) + ") has " + str(total_games) + " games played, " + str(win) + " wins, " + str(loss) + " losses.\nWinrate: " + str(winrate) + "%\nStreak: 0.")
                await ctx.channel.send("**" + name + "** has played **" + str(total_games) + "** games with a win rate of **" + str(winrate) + "%** (**" + str(win) + "**W - **" + str(loss) + "**L). Their ELO: **" + str(pts) + "**. Sigma: **" + str(sigma) + "**. Streak: **" + str(streak) + "**. Rank: **" + str(rank) + "**.")
                # embed = discord.Embed(
                #     colour = 0x1F1E1E
                # )
                # embed.add_field(name="Statistics\n\u200b", value=f'**{name}** has played a total of **{total_games}** games with a win rate of **{winrate}**%\nCurrent win streak: **{winstreak}**; Current loss streak: **{loss_streak}**; Warnings: **{warns}**', inline=False)
                # embed.add_field(name='\n\u200b', value=f'ELO: **{pts}**')
                # embed.add_field(name='\n\u200b', value=f'Wins: **{win}**')
                # embed.add_field(name='\n\u200b', value=f'Losses: **{loss}**')

                # await ctx.channel.send(embed=embed)
                # embed = discord.Embed(
                #     colour=0x1F1E1E
                # )
                # embed.set_thumbnail(url=url)
                # embed.add_field(name=f"{name}\n\u200b",
                #                 value=f'**{name}** has played a total of **{total_games}** games with a win rate of **{winrate}**%',
                #                 inline=False)
                # embed.add_field(name='\n\u200b', value=f'ELO: **{pts}**')
                # embed.add_field(name='\n\u200b', value=f'Wins: **{win}**')
                # embed.add_field(name='\n\u200b', value=f'Losses: **{loss}**')
                # embed.add_field(name='\n\u200b', value=f'Streak: **{streak}**')
                # embed.add_field(name='\n\u200b', value=f'Warnings: **{warns}**/**4**')
                # embed.add_field(name='\n\u200b', value=f'Peak: **{peak}**\n')
                # embed.add_field(name='\n\u200b', value=f"**Additional Information**\n\n{description}")
                # embed.set_footer(text="\n\u200bTip: You can change your profile picture by typing !profile add link.")
                # embed.set_footer(text="Tip: [You can change your picture by typing !profile add (link)](https://cdn1.bbcode0.com/uploads/2020/7/1/888ce487a07a840bf8f6c2bc7f842252-full.jpg")
                # await ctx.send(embed=embed)
        else:
            await ctx.channel.send("No user found by that name!")

        conn.commit()
        conn.close()

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def warns(ctx, player=None):

    '''Show's warnings on a player'''

    global joined_dic

    test_channel = discord.Object(785006530310438912)

    if ctx.channel.id == ones_channel.id or test_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        t = ctx.author.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT fresh_warns, name FROM players WHERE ID = ?", [t])
        fetch = c.fetchone()
        warns = fetch[0]
        name = fetch[1]

        c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings WHERE ID = ?", [t])
        fetch5 = c.fetchone()
        reasonone = fetch5[0]
        reasontwo = fetch5[1]
        reasonthree = fetch5[2]
        timeone = fetch5[3]
        timetwo = fetch5[4]
        timethree = fetch5[5]


        if player == None:

            if warns == 0:
                await ctx.send(f"{name} has {warns} warnings.")

            if warns > 0:

                if reasontwo == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\nNext unwarn in ")
                    return

                if reasonthree == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\nNext unwarn in ")            
                    return

                else:

                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\n[3] {reasonthree} on {timethree}\nNext unwarn in ")
                    return

        elif player:

            player = find_userid_by_name(ctx, player)

            if player is None:
                await ctx.channel.send(f"'{player}' not found.")
                return

            c.execute("SELECT name, fresh_warns FROM players WHERE ID = ?", [player])
            fetch2 = c.fetchone()
            player_warns = fetch2[1]
            player_name = fetch2[0]

            c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings WHERE ID = ?", [player])
            fetch3 = c.fetchone()
            reason1 = fetch3[0]
            reason2 = fetch3[1]
            reason3 = fetch3[2]
            time1 = fetch3[3]
            time2 = fetch3[4]
            time3 = fetch3[5]

            if player_warns == 0:
                await ctx.send(f"{player_name} has {warns} warnings.")
                return
            
            if player_warns > 0:

                # If you have all 3 warns:

                if reason1 is not None and reason2 is not None and reason3 is not None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 1 and 2 only:

                if reason1 is not None and reason2 is not None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have warns 1 and 3 only:

                if reason1 is not None and reason3 is not None and reason2 == None:

                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 3 and 2 only:

                if reason3 is not None and reason2 is not None and reason1 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you only the 3rd warn:

                if reason1 == None and reason2 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have only the 2nd warn:

                if reason1 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have only the 1st warn:

                if reason2 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\nNext unwarn in ")

                return
                    
        conn.close()

    if ctx.channel.id == twos_channel.id or test_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        t = ctx.author.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT fresh_warns, name FROM players_team WHERE ID = ?", [t])
        fetch = c.fetchone()
        warns = fetch[0]
        name = fetch[1]

        c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings2 WHERE ID = ?", [t])
        fetch5 = c.fetchone()
        reasonone = fetch5[0]
        reasontwo = fetch5[1]
        reasonthree = fetch5[2]
        timeone = fetch5[3]
        timetwo = fetch5[4]
        timethree = fetch5[5]


        if player == None:

            if warns == 0:
                await ctx.send(f"{name} has {warns} warnings.")

            if warns > 0:

                if reasontwo == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\nNext unwarn in ")
                    return

                if reasonthree == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\nNext unwarn in ")            
                    return

                else:

                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\n[3] {reasonthree} on {timethree}\nNext unwarn in ")
                    return

        elif player:

            player = find_userid_by_name(ctx, player)

            if player is None:
                await ctx.channel.send(f"'{player}' not found.")
                return

            c.execute("SELECT name, fresh_warns FROM players_team WHERE ID = ?", [player])
            fetch2 = c.fetchone()
            player_warns = fetch2[1]
            player_name = fetch2[0]

            c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings2 WHERE ID = ?", [player])
            fetch3 = c.fetchone()
            reason1 = fetch3[0]
            reason2 = fetch3[1]
            reason3 = fetch3[2]
            time1 = fetch3[3]
            time2 = fetch3[4]
            time3 = fetch3[5]

            if player_warns == 0:
                await ctx.send(f"{player_name} has {warns} warnings.")
                return
            
            if player_warns > 0:

                # If you have all 3 warns:

                if reason1 is not None and reason2 is not None and reason3 is not None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 1 and 2 only:

                if reason1 is not None and reason2 is not None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have warns 1 and 3 only:

                if reason1 is not None and reason3 is not None and reason2 == None:

                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 3 and 2 only:

                if reason3 is not None and reason2 is not None and reason1 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you only the 3rd warn:

                if reason1 == None and reason2 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have only the 2nd warn:

                if reason1 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have only the 1st warn:

                if reason2 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\nNext unwarn in ")

                return
                    
        conn.close()

    if ctx.channel.id == threes_channel.id or test_channel.id:

        x = ctx.author.id
        joined_dic[x] = gettime()

        t = ctx.author.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT fresh_warns, name FROM players_team WHERE ID = ?", [t])
        fetch = c.fetchone()
        warns = fetch[0]
        name = fetch[1]

        c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings3 WHERE ID = ?", [t])
        fetch5 = c.fetchone()
        reasonone = fetch5[0]
        reasontwo = fetch5[1]
        reasonthree = fetch5[2]
        timeone = fetch5[3]
        timetwo = fetch5[4]
        timethree = fetch5[5]


        if player == None:

            if warns == 0:
                await ctx.send(f"{name} has {warns} warnings.")

            if warns > 0:

                if reasontwo == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\nNext unwarn in ")
                    return

                if reasonthree == None:
                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\nNext unwarn in ")            
                    return

                else:

                    await ctx.send(f"{name} has {warns} warnings:\n[1] {reasonone} on {timeone}\n[2] {reasontwo} on {timetwo}\n[3] {reasonthree} on {timethree}\nNext unwarn in ")
                    return

        elif player:

            player = find_userid_by_name(ctx, player)

            if player is None:
                await ctx.channel.send(f"'{player}' not found.")
                return

            c.execute("SELECT name, fresh_warns FROM players_team WHERE ID = ?", [player])
            fetch2 = c.fetchone()
            player_warns = fetch2[1]
            player_name = fetch2[0]

            c.execute("SELECT reason1, reason2, reason3, time_of_warn1, time_of_warn2, time_of_warn3 FROM warnings3 WHERE ID = ?", [player])
            fetch3 = c.fetchone()
            reason1 = fetch3[0]
            reason2 = fetch3[1]
            reason3 = fetch3[2]
            time1 = fetch3[3]
            time2 = fetch3[4]
            time3 = fetch3[5]

            if player_warns == 0:
                await ctx.send(f"{player_name} has {warns} warnings.")
                return
            
            if player_warns > 0:

                # If you have all 3 warns:

                if reason1 is not None and reason2 is not None and reason3 is not None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 1 and 2 only:

                if reason1 is not None and reason2 is not None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have warns 1 and 3 only:

                if reason1 is not None and reason3 is not None and reason2 == None:

                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have warns 3 and 2 only:

                if reason3 is not None and reason2 is not None and reason1 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you only the 3rd warn:

                if reason1 == None and reason2 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[3] {reason3} on {time3}\nNext unwarn in ")

                # If you have only the 2nd warn:

                if reason1 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[2] {reason2} on {time2}\nNext unwarn in ")

                # If you have only the 1st warn:

                if reason2 == None and reason3 == None:
                    await ctx.send(f"{player_name} has {player_warns} warnings:\n[1] {reason1} on {time1}\nNext unwarn in ")

                return
                    
        conn.close()

@client.command()
@commands.cooldown(1, 2, commands.BucketType.user)
async def compare(ctx, p1, p2):

    """Compares two users statistics.""" 

    global PLAYERS, db_path, joined_dic

    if ctx.channel.id == ones_channel.id:

        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()

        x = ctx.author.id
        joined_dic[x] = gettime()
        
        t1 = find_userid_by_name(ctx, p1)
        if t1 is None:
            await ctx.channel.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            conn.close()
            return
        
        c.execute("SELECT name, elo, sigma FROM players where ID = ?", [t1])
        result = c.fetchone()
        if result is None:
            await ctx.channel.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            conn.close()
            return
        name1 = result[0]
        elo1 = float(result[1])
        sigma1 = float(result[2])
        

        t2 = find_userid_by_name(ctx, p2)
        if t2 is None:
            await ctx.channel.send("No user found by the name \"" + p2 + "\"!")
            conn.commit()
            conn.close()
            return
        
        c.execute("SELECT name, elo, sigma FROM players where ID = ?", [t2])
        result = c.fetchone()
        if result is None:
            await ctx.channel.send("No user found by the name \"" + p2 + "\"!")
            conn.commit()
            conn.close()
            return
        name2 = result[0]
        elo2 = float(result[1])
        sigma2 = float(result[2])
        
        wins = 0
        losses = 0
        
        c.execute("SELECT s1 FROM games WHERE (p1 == ? AND p2 == ? AND p3 IS NULL) AND s1 != s2", [t1, t2])
        game = c.fetchone()
        while game is not None:
            result = game[0]
            if result == "won":
                wins += 1
            elif result == "lost":
                losses += 1
            else:
                # shouldn't happen, maybe error or print to terminal
                pass
            
            game = c.fetchone()
        
        c.execute("SELECT s2 FROM games WHERE (p1 == ? AND p2 == ? AND p3 IS NULL) AND s1 != s2", [t2, t1])
        game = c.fetchone()
        while game is not None:
            result = game[0]
            if result == "won":
                wins += 1
            elif result == "lost":
                losses += 1
            else:
                # shouldn't happen, maybe error or print to terminal
                pass
            
            game = c.fetchone()

        def erfc(x):
            """Complementary error function (via `http://bit.ly/zOLqbc`_)"""
            z = abs(x)
            t = 1. / (1. + z / 2.)
            r = t * np.math.exp(-z * z - 1.26551223 + t * (1.00002368 + t * (
                0.37409196 + t * (0.09678418 + t * (-0.18628806 + t * (
                    0.27886807 + t * (-1.13520398 + t * (1.48851587 + t * (
                        -0.82215223 + t * 0.17087277
                    )))
                )))
            )))
            return 2. - r if x < 0 else r


        def cdf(x, mu=0, sigma=1):
            """Cumulative distribution function"""
            return 0.5 * erfc(-(x - mu) / (sigma * np.math.sqrt(2)))

        # win_probability
        BETA=200
        deltaMu = elo1 - elo2
        sumSigma = sigma1**2 + sigma2**2
        rsss = np.sqrt(2* (BETA**2) + sumSigma)
        win_probability = cdf(deltaMu/rsss)

        if wins + losses > 0:
            s = f"{name1} (Elo: {int(round(elo1))}, Sigma: {int(round(sigma1))}) and {name2} (Elo: {int(round(elo2))}, Sigma: {int(round(sigma2))}) have played a total of {wins + losses} games together.\n"
            s += f"{name1} has a win rate of {wins/(wins+losses)*100:.2f}% (**{wins}W - {losses}L**) against {name2}.\n"
        else:
            s = f"{name1} (Elo: {int(round(elo1))}, Sigma: {int(round(sigma1))}) and {name2} (Elo: {int(round(elo2))}, Sigma: {int(round(sigma2))}) have not played any games together.\n"

        s += f"{name1}'s expected win probability against {name2} is {win_probability*100:.2f}%."
        
        await ctx.channel.send(s)
        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id or ctx.channel.id == twos_channel:

        conn = sqlite3.connect(db_path, uri=True)
        c = conn.cursor()

        x = ctx.author.id
        joined_dic[x] = gettime()
        
        t1 = find_userid_by_name(ctx, p1)
        if t1 is None:
            await ctx.channel.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            conn.close()
            return
        
        c.execute("SELECT name, elo FROM players_team where ID = ?", [t1])
        result = c.fetchone()
        if result is None:
            await ctx.channel.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            conn.close()
            return
        name1 = result[0]
        elo1 = str(result[1])
        

        t2 = find_userid_by_name(ctx, p2)
        if t2 is None:
            await ctx.channel.send("No user found by the name \"" + p2 + "\"!")
            conn.commit()
            conn.close()
            return
        
        c.execute("SELECT name, elo FROM players_team where ID = ?", [t2])
        result = c.fetchone()
        if result is None:
            await ctx.channel.send("No user found by the name \"" + p2 + "\"!")
            conn.commit()
            conn.close()
            return
        name2 = result[0]
        elo2 = str(result[1])
        
        wins_together = 0
        loss_together = 0
        wins_against  = 0
        loss_against  = 0
        
        c.execute("SELECT s1, s2, ID FROM games_team where (p1 == ? OR p2 == ? OR p3 == ? OR p4 == ?) AND (p1 == ? OR p2 == ? OR p3 == ? OR p4 == ?) AND s1 != s2", [t1, t1, t1, t1, t2, t2, t2, t2])
        game = c.fetchone()
        while game is not None:
            s1 = game[0]
            s2 = game[1]
            if s1 > s2:
                wins_together += 1
            elif s1 < s2:
                loss_together += 1  
            
            game = c.fetchone()
        
        c.execute("SELECT s1, s2, ID FROM games_team where (p5 == ? OR p6 == ? OR p7 == ? OR p8 == ?) AND (p5 == ? OR p6 == ? OR p7 == ? OR p8 == ?) AND s1 != s2", [t1, t1, t1, t1, t2, t2, t2, t2])
        game = c.fetchone()
        while game is not None:
            s1 = game[0]
            s2 = game[1]
            
            if s1 < s2:
                wins_together += 1
            elif s1 > s2:
                loss_together += 1
            
            game = c.fetchone()

        c.execute("SELECT s1, s2 FROM games_team where (p1 == ? OR p2 == ? OR p3 == ? OR p4 == ?) AND (p5 == ? OR p6 == ? OR p7 == ? OR p8 == ?) AND s1 != s2", [t1, t1, t1, t1, t2, t2, t2, t2])
        game = c.fetchone()
        while game is not None:
            s1 = game[0]
            s2 = game[1]
            
            if s1 > s2:
                wins_against += 1
            elif s1 < s2:
                loss_against += 1
            
            game = c.fetchone()
        
        c.execute("SELECT s1, s2 FROM games_team where (p5 == ? OR p6 == ? OR p7 == ? OR p8 == ?) AND (p1 == ? OR p2 == ? OR p3 == ? OR p4 == ?) AND s1 != s2", [t1, t1, t1, t1, t2, t2, t2, t2])
        game = c.fetchone()
        while game is not None:
            s1 = game[0]
            s2 = game[1]
            
            if s1 < s2:
                wins_against += 1
            elif s1 > s2:
                loss_against += 1
            
            game = c.fetchone()

        total_together = wins_together + loss_together
        if total_together > 0:
            winrate_together = float("{0:.2f}".format((wins_together / total_together) * 100))
            str_together = name1 + " **[" + elo1 + "]** and " + name2 + " **[" + elo2 + "]** have played " + str(total_together) + " games together with a win rate of " + str(winrate_together) + "% (**" + str(wins_together) + "W - " + str(loss_together) + "L**)."
        else:
            str_together = name1 + " **[" + elo1 + "]** and " + name2 + " **[" + elo2 + "]** have not played together."
        
        total_against = wins_against + loss_against
        if total_against > 0:
            winrate_against = float("{0:.2f}".format((wins_against / total_against) * 100))
            str_against = name1 + " **[" + elo1 + "]** has played against " + name2 + " **[" + elo2 + "]** a total of " + str(total_against) + " times with a win rate of " + str(winrate_against) + "% (**" + str(wins_against) + "W - " + str(loss_against) + "L**) ."
        else:
            str_against = name1 + " **[" + elo1 + "]** and " + name2 + " **[" + elo2 + "]** have not played against each other."
        
        
        await ctx.channel.send(str_together + "\n" + str_against)
        conn.commit()
        conn.close()


@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin', 'PwR Team')
async def set_elo(ctx, name, adjustment):
    '''Adjusts a players ELO.'''

    global db_path

    if ctx.channel.id == ones_channel.id:
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, elo FROM players WHERE ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            adjust = int(adjustment)
            name = player[0]
            elo = player[1]
            c.execute("UPDATE players SET elo = ?, elo_adjustments = elo_adjustments + ? WHERE ID = ?",
                      [adjust, adjust, t])

            out = "**" + ctx.message.author.name + "** has "
            if adjust > 0:
                out += "given **" + adjustment + "** ELO to**"
            else:
                out += "removed " + str(adjust * -1) + " ELO from **"
            out += " " + name + "**! They now have an ELO of **" + str(int(adjust)) + "**!"
            activity_channel = client.get_channel(790313358816968715)
            await ctx.channel.send(out)
            await activity_channel.send(out)
        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, elo FROM players_team WHERE ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            adjust = int(adjustment)
            name = player[0]
            elo = player[1]
            c.execute("UPDATE players_team SET elo = ?, elo_adjustments = elo_adjustments + ? WHERE ID = ?",
                      [adjust, adjust, t])

            out = "**" + ctx.message.author.name + "** has "
            if adjust > 0:
                out += "given **" + adjustment + "** ELO to**"
            else:
                out += "removed " + str(adjust * -1) + " ELO from **"
            out += " " + name + "**! They now have an ELO of **" + str(int(adjust)) + "**!"
            activity_channel = client.get_channel(790313358816968715)
            await ctx.channel.send(out)
            await activity_channel.send(out)
        conn.commit()
        conn.close()

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin', 'PwR Team')
async def set_sigma(ctx, name, adjustment):
    '''Adjusts a players ELO.'''

    global db_path

    if ctx.channel.id == ones_channel.id:
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, sigma FROM players WHERE ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            adjust = int(adjustment)
            name = player[0]
            elo = player[1]
            c.execute("UPDATE players SET sigma = ?, elo_adjustments = elo_adjustments + ? WHERE ID = ?",
                      [adjust, adjust, t])

            out = "**" + ctx.message.author.name + "** has "
            if adjust > 0:
                out += "given **" + adjustment + "** SIGMA to**"
            else:
                out += "removed " + str(adjust * -1) + " SIGMA from **"
            out += " " + name + "**! They now have an SIGMA of **" + str(int(adjust)) + "**!"
            activity_channel = client.get_channel(790313358816968715)
            await ctx.channel.send(out)
            await activity_channel.send(out)
        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.channel.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, sigma FROM players_team WHERE ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            adjust = int(adjustment)
            name = player[0]
            elo = player[1]
            c.execute("UPDATE players_team SET sigma = ?, elo_adjustments = elo_adjustments + ? WHERE ID = ?",
                      [adjust, adjust, t])

            out = "**" + ctx.message.author.name + "** has "
            if adjust > 0:
                out += "given **" + adjustment + "** SIGMA to**"
            else:
                out += "removed " + str(adjust * -1) + " SIGMA from **"
            out += " " + name + "**! They now have an SIGMA of **" + str(int(adjust)) + "**!"
            activity_channel = client.get_channel(790313358816968715)
            await ctx.channel.send(out)
            await activity_channel.send(out)
        conn.commit()
        conn.close()

@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
@commands.has_any_role('League Admin', 'PwR Team')
async def update_leaderboards(ctx):
    """ Manually updates the leaderboard."""

    if ctx.channel.id == ones_channel.id or ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:

        await leaderboard_solo(ctx)
        await leaderboard_team(ctx)
        t = ctx.message.author.name
        activity_channel = client.get_channel(790313358816968715)
        await ctx.channel.send(str(t) + " has updated the leaderboard.")
        await activity_channel.send(str(t) + " has updated the leaderboard.")


@client.command()
@commands.has_any_role('League Admin')
async def warn(ctx, name, *, reason, aliases=["w", "aw", "warns", "addwarn", "addwarns"]):
    '''Warns a player.'''

    global warned

    if ctx.channel.id == ones_channel.id:
            
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, id FROM players where ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            name = player[0]
            warns = player[1] + player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if reason is not None:
                if warns is None:
                    warns = 0

                time = datetime.datetime.now()

                time_data = time.strftime("%B"),time.strftime("%d") + ", " + time.strftime("%Y"), time.strftime("%I") + ":" + time.strftime("%M") + " " + time.strftime("%p")

                if warns == 0:

                    new_warns = warns
                    c.execute("UPDATE players SET fresh_warns = ? where ID = ?", [1, t])
                    c.execute("UPDATE warnings SET reason1 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings SET time_of_warn1 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warning"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0
                    warn_dic[t] = gettime()
                    warned.append(t)


                if warns == 1:
                    
                    new_warns = warns
                    c.execute("UPDATE players SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings SET reason2 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings SET time_of_warn2 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if warns == 2:
                    
                    new_warns = warns
                    c.execute("UPDATE players SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings SET reason3 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings SET time_of_warn3 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if user is not None:
                    pass

                reason = "{}".format(reason)

                if warns >= 3:
                    out += " and remain **banned**"

                elif warns >= 3:
                    out += " and are now **banned**"


                await ctx.send(out + ".")
                activity_channel = client.get_channel(790313358816968715)
                await activity_channel.send(activity_out + ".")

            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:
            
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, id FROM players_team where ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            name = player[0]
            warns = player[1] + player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if reason is not None:
                if warns is None:
                    warns = 0

                time = datetime.datetime.now()

                time_data = time.strftime("%B"),time.strftime("%d") + ", " + time.strftime("%Y"), time.strftime("%I") + ":" + time.strftime("%M") + " " + time.strftime("%p")

                if warns == 0:

                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = ? where ID = ?", [1, t])
                    c.execute("UPDATE warnings2 SET reason1 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings2 SET time_of_warn1 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warning"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0
                    warn_dic[t] = gettime()
                    warned.append(t)


                if warns == 1:
                    
                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings2 SET reason2 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings2 SET time_of_warn2 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if warns == 2:
                    
                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings2 SET reason3 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings2 SET time_of_warn3 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if user is not None:
                    pass

                reason = "{}".format(reason)

                if warns >= 3:
                    out += " and remain **banned**"

                elif warns >= 3:
                    out += " and are now **banned**"


                await ctx.send(out + ".")
                activity_channel = client.get_channel(790313358816968715)
                await activity_channel.send(activity_out + ".")

            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:
            
        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, id FROM players_team where ID = ?", [t])
        player = c.fetchone()

        if player is not None:
            name = player[0]
            warns = player[1] + player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if reason is not None:
                if warns is None:
                    warns = 0

                time = datetime.datetime.now()

                time_data = time.strftime("%B"),time.strftime("%d") + ", " + time.strftime("%Y"), time.strftime("%I") + ":" + time.strftime("%M") + " " + time.strftime("%p")

                if warns == 0:

                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = ? where ID = ?", [1, t])
                    c.execute("UPDATE warnings3 SET reason1 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings3 SET time_of_warn1 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warning"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0
                    warn_dic[t] = gettime()
                    warned.append(t)


                if warns == 1:
                    
                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings3 SET reason2 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings3 SET time_of_warn2 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if warns == 2:
                    
                    new_warns = warns
                    c.execute("UPDATE players_team SET fresh_warns = fresh_warns + 1 where ID = ?", [t])
                    c.execute("UPDATE warnings3 SET reason3 = ? WHERE ID = ?", [reason + " by " + ctx.author.name, t])
                    c.execute("UPDATE warnings3 SET time_of_warn3 = ? WHERE ID = ?", [time_data[0] + " " + time_data[1] + " " + time_data[2], t])
                    new_warns = new_warns + 1
                    out = f"<@{t}> a warning has been issued by **{ctx.author.name}** for {reason}. You now have **{new_warns}** warnings"
                    activity_out = f"**{ctx.message.author.name}** has issued **1** warnings to **{name}** for {reason}. \nThey now have **{new_warns}** warnings"
                    new_warns = 0

                if user is not None:
                    pass

                reason = "{}".format(reason)

                if warns >= 3:
                    out += " and remain **banned**"

                elif warns >= 3:
                    out += " and are now **banned**"


                await ctx.send(out + ".")
                activity_channel = client.get_channel(790313358816968715)
                await activity_channel.send(activity_out + ".")

            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()
        
@client.command(aliases=["rw", "removewarn"])
@commands.has_any_role('League Admin')
async def unwarn(ctx, name, warnings=None):
    '''Unwarns a player.'''

    if ctx.channel.id == ones_channel.id:

        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, ID FROM players where ID = ?", [t])
        player = c.fetchone()

        c.execute("SELECT reason1,reason2,reason3 FROM warnings WHERE ID = ?", [t])
        row = c.fetchone()
        reason1 = row[0]
        reason2 = row[1]
        reason3 = row[2]

        if player is not None:
            name = player[0]
            warns = player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if int(warnings) > 0:
                if warns is None:
                    warns = 0

                if warns == 1:

                    if int(warnings) == 1:
                            
                        c.execute("UPDATE warnings SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:

                        c.execute("UPDATE warnings SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"



                if warns == 2:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:
                            
                        c.execute("UPDATE warnings SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if warns == 3:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:

                        c.execute("UPDATE warnings SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"
                        
                    if int(warnings) == 3:

                        c.execute("UPDATE warnings SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if user is not None:
                    pass

                if warns >= 3:
                    out += " and remain **banned**"
                elif warns >= 3:
                    out += " and are now **unbanned**"

                activity_channel = client.get_channel(790313358816968715)
                await ctx.send(out + ".")
                if ctx.message.channel.id != admin_channel.id:
                    await activity_channel.send(activity_out + ".")
            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, ID FROM players_team where ID = ?", [t])
        player = c.fetchone()

        c.execute("SELECT reason1,reason2,reason3 FROM warnings2 WHERE ID = ?", [t])
        row = c.fetchone()
        reason1 = row[0]
        reason2 = row[1]
        reason3 = row[2]

        if player is not None:
            name = player[0]
            warns = player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if int(warnings) > 0:
                if warns is None:
                    warns = 0

                if warns == 1:

                    if int(warnings) == 1:
                            
                        c.execute("UPDATE warnings2 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings2 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:

                        c.execute("UPDATE warnings2 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"



                if warns == 2:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings2 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings2 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:
                            
                        c.execute("UPDATE warnings2 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if warns == 3:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings2 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:

                        c.execute("UPDATE warnings2 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"
                        
                    if int(warnings) == 3:

                        c.execute("UPDATE warnings2 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings2 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if user is not None:
                    pass

                if warns >= 3:
                    out += " and remain **banned**"
                elif warns >= 3:
                    out += " and are now **unbanned**"

                activity_channel = client.get_channel(790313358816968715)
                await ctx.send(out + ".")
                if ctx.message.channel.id != admin_channel.id:
                    await activity_channel.send(activity_out + ".")
            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:

        t = find_userid_by_name(ctx, name)
        if t is None:
            await ctx.send("No user found by that name!")
            return

        user = find_user_by_name(ctx, name)

        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("SELECT name, warnings, fresh_warns, ID FROM players_team where ID = ?", [t])
        player = c.fetchone()

        c.execute("SELECT reason1,reason2,reason3 FROM warnings3 WHERE ID = ?", [t])
        row = c.fetchone()
        reason1 = row[0]
        reason2 = row[1]
        reason3 = row[2]

        if player is not None:
            name = player[0]
            warns = player[2]
            stale_warns = player[1]
            fresh_warns = player[2]
            ids = player[3]

            if int(warnings) > 0:
                if warns is None:
                    warns = 0

                if warns == 1:

                    if int(warnings) == 1:
                            
                        c.execute("UPDATE warnings3 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings3 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:

                        c.execute("UPDATE warnings3 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"



                if warns == 2:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings3 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:
                            
                        c.execute("UPDATE warnings3 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 3:
                            
                        c.execute("UPDATE warnings3 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if warns == 3:

                    if int(warnings) == 1:

                        c.execute("UPDATE warnings3 SET reason1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn1 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason1}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason1}.\nThey now have **{warns}** warnings"

                    if int(warnings) == 2:

                        c.execute("UPDATE warnings3 SET reason2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn2 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason2}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason2}.\nThey now have **{warns}** warnings"
                        
                    if int(warnings) == 3:

                        c.execute("UPDATE warnings3 SET reason3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE warnings3 SET time_of_warn3 = NULL WHERE ID = ?", [t])
                        c.execute("UPDATE players_team SET fresh_warns = fresh_warns - 1 where ID = ?", [t])
                        warns = warns - 1
                        out = f"<@{t}> a warning has been removed by **{ctx.message.author.name}** for {reason3}. You now have {warns} warnings"
                        activity_out = f"**{ctx.message.author.name}** has removed a warning from {name} for {reason3}.\nThey now have **{warns}** warnings"

                if user is not None:
                    pass

                if warns >= 3:
                    out += " and remain **banned**"
                elif warns >= 3:
                    out += " and are now **unbanned**"

                activity_channel = client.get_channel(790313358816968715)
                await ctx.send(out + ".")
                if ctx.message.channel.id != admin_channel.id:
                    await activity_channel.send(activity_out + ".")
            else:
                await ctx.send("Warn amount must be positive.")
        else:
            await ctx.send("No user found by that name!")

        conn.commit()
        conn.close()

@client.command()
@commands.has_any_role("League Admin")
async def update_nickname(ctx, player: discord.Member, nickname):

    """Updates a players nickname."""

    if ctx.channel.id == ones_channel.id:

        playerID = player.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("UPDATE players SET name = ? WHERE ID = ?", [nickname, playerID])
        await ctx.send("Nickname updated.")
        conn.commit()
        conn.close()

    if ctx.channel.id == twos_channel.id:

        playerID = player.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("UPDATE players_team SET name = ? WHERE ID = ?", [nickname, playerID])
        await ctx.send("Nickname updated.")
        conn.commit()
        conn.close()

    if ctx.channel.id == threes_channel.id:

        playerID = player.id
        conn = sqlite3.connect(db_path)
        c = conn.cursor()
        c.execute("UPDATE players_team SET name = ? WHERE ID = ?", [nickname, playerID])
        await ctx.send("Nickname updated.")
        conn.commit()
        conn.close()

@client.command()
@commands.cooldown(1,2,commands.BucketType.user)
async def farmed(ctx, p1=None):
    """ Display Users Personal Stats. """

    try:
        conn = sqlite3.connect(db_path)
        strMessage = ""
        c = conn.cursor()

        if(p1 == ""):
            p1 = ctx.message.author.id

        t1 = find_userid_by_name(ctx, p1)

        if t1 is None:
            await ctx.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            return

        sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
and (GF + GA != 0 ) "

        c.execute(sql, [t1])
        data = c.fetchall()
        GF = data[0][0]
        GA = data[0][1]
        PlusMinus = data[0][2]
        name = data[0][3]
        elo = data[0][4]

        strMessage = "**" + name + " [" + str(elo) + "]** was farmed by:\n" \
                    #"ELO: " + str(elo) + ", Average Goals For: " + str(round(GF,2)) + ", Average Goals Against: " + str(round(GA, 2)) + ", Net: " + str(round(PlusMinus,2))

        sql = "select sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100, pg2.Name from playergames pg1 \
left join playergames as pg2 on pg2.ID = pg1.ID \
and pg1.pID != pg2.pID \
 where pg1.pID = ? and (pg1.GF + pg1.GA) != 0  and (pg1.teamID != pg2.teamID) \
group by pg2.pid, pg2.pid \
having count(*) >= 5 and (sUM(case when pg1.GF > PG1.GA then 0 ELSE 1 enD) / (COUNT(*) * 1.00) * 100) > 50 ORDER BY sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) ASC limit 5 "

        c.execute(sql, [t1])
        data = c.fetchall()
        print(data)
        if len(data) > 0:
            strMessage += ""
            first = True
            for game in data:
                if first:
                    first = False
                else:
                    strMessage += "\n"
                strMessage += game[1] + " (" + str(round(game[0], 2)) + "%)"

        await ctx.send(strMessage)

        conn.commit()
    except: 

        try:
            conn = sqlite3.connect(db_path)
            strMessage = "\n"
            c = conn.cursor()

            if(p1 == ""):
                p1 = ctx.message.author.id

            t1 = ctx.author.id

            if t1 is None:
                await ctx.send("No user found by the name \"" + p1 + "\"!")
                conn.commit()
                return

            sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
    AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
    and (GF + GA != 0 ) "

            c.execute(sql, [t1])
            data = c.fetchall()
            GF = data[0][0]
            GA = data[0][1]
            PlusMinus = data[0][2]
            name = data[0][3]
            elo = data[0][4]

            strMessage = "**" + name + " [" + str(elo) + "]** was farmed by:\n" \
                        #"ELO: " + str(elo) + ", Average Goals For: " + str(round(GF,2)) + ", Average Goals Against: " + str(round(GA, 2)) + ", Net: " + str(round(PlusMinus,2))

            sql = "select sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100, pg2.Name from playergames pg1 \
    left join playergames as pg2 on pg2.ID = pg1.ID \
    and pg1.pID != pg2.pID \
    where pg1.pID = ? and (pg1.GF + pg1.GA) != 0  and (pg1.teamID != pg2.teamID) \
    group by pg2.pid, pg2.pid \
    having count(*) >= 5 and (sUM(case when pg1.GF > PG1.GA then 0 ELSE 1 enD) / (COUNT(*) * 1.00) * 100) > 50 ORDER BY sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) ASC limit 5 "

            c.execute(sql, [t1])
            data = c.fetchall()
            print(data)
            c.execute("SELECT elo FROM players WHERE name = ?", [data[0][1]])
            elos = c.fetchone()[0]
            print(elos)
            print(data[0][1])
            if len(data) > 0:
                strMessage += ""
                first = True
                for game in data:
                    if first:
                        first = False
                    else:
                        strMessage += "\n"
                    strMessage += game[1] + " (" + str(round(game[0], 2)) + "%)"

            await ctx.send(strMessage)

            conn.commit()
        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            logger.error(str(exc_type) + "\n\n" + str(exc_obj) + "\n\n" + "Line: " + str(exc_tb.tb_lineno))

@client.command()
@commands.cooldown(1,2,commands.BucketType.user)
async def farm(ctx, p1=None):
    """ Display Users Personal Stats. """

    try:
        conn = sqlite3.connect(db_path)
        strMessage = ""
        c = conn.cursor()

        if(p1 == ""):
            p1 = ctx.message.author.id

        t1 = find_userid_by_name(ctx, p1)

        if t1 is None:
            await ctx.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            return

        sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
and (GF + GA != 0 ) "

        c.execute(sql, [t1])
        data = c.fetchall()
        GF = data[0][0]
        GA = data[0][1]
        PlusMinus = data[0][2]
        name = data[0][3]
        elo = data[0][4]

        strMessage = "**" + name + " [" + str(elo) + "]** farmed:\n" \

        sql = "select sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100, pg2.name from playergames pg1 \
left join playergames as pg2 on pg2.ID = pg1.ID \
and pg1.pID != pg2.pID \
 where pg1.pID = ? and (pg1.GF + pg1.GA) != 0  and (pg1.teamID != pg2.teamID) \
group by pg2.pid, pg2.pid \
having count(*) >= 5 and ( sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100) > 50 ORDER BY sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) DESC limit 5 "

        c.execute(sql, [t1])
        data = c.fetchall()
        if len(data) > 0:
            strMessage += ""
            first = True
            for game in data:
                if first:
                    first = False
                else:
                    strMessage += "\n"
                strMessage += game[1] + " (" + str(round(game[0], 2)) + "%)"

        await ctx.send(strMessage)

        conn.commit()
    except: 

        try:
            conn = sqlite3.connect(db_path)
            strMessage = ""
            c = conn.cursor()

            if(p1 == ""):
                p1 = ctx.message.author.id

            t1 = ctx.author.id

            if t1 is None:
                await ctx.send("No user found by the name \"" + p1 + "\"!")
                conn.commit()
                return

            sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
    AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
    and (GF + GA != 0 ) "

            c.execute(sql, [t1])
            data = c.fetchall()
            GF = data[0][0]
            GA = data[0][1]
            PlusMinus = data[0][2]
            name = data[0][3]
            elo = data[0][4]

            strMessage = "**" + name + " [" + str(elo) + "]** farmed:\n" \

            sql = "select sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100, pg2.name from playergames pg1 \
    left join playergames as pg2 on pg2.ID = pg1.ID \
    and pg1.pID != pg2.pID \
    where pg1.pID = ? and (pg1.GF + pg1.GA) != 0  and (pg1.teamID != pg2.teamID) \
    group by pg2.pid, pg2.pid \
    having count(*) >= 5 and ( sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) * 100) > 50 ORDER BY sUM(case when pg1.GF > PG1.GA then 1 ELSE 0 enD) / (COUNT(*) * 1.00) DESC limit 5 "

            c.execute(sql, [t1])
            data = c.fetchall()
            if len(data) > 0:
                strMessage += ""
                first = True
                for game in data:
                    if first:
                        first = False
                    else:
                        strMessage += "\n"
                    strMessage += game[1] + " (" + str(round(game[0], 2)) + "%)"

            await ctx.send(strMessage)

            conn.commit()
        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            logger.error(str(exc_type) + "\n\n" + str(exc_obj) + "\n\n" + "Line: " + str(exc_tb.tb_lineno))

@client.command()
@commands.cooldown(1,2,commands.BucketType.user)
async def worst(ctx, p1=None):
    """ Display Users Personal Stats. """

    try:
        conn = sqlite3.connect(db_path)
        strMessage = ""
        c = conn.cursor()

        if(p1 == ""):
            p1 = ctx.message.author.id

        t1 = find_userid_by_name(ctx, p1)

        if t1 is None:
            await ctx.send("No user found by the name \"" + p1 + "\"!")
            conn.commit()
            return

        sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
and (GF + GA != 0 ) "

        c.execute(sql, [t1])
        data = c.fetchall()
        GF = data[0][0]
        GA = data[0][1]
        PlusMinus = data[0][2]
        name = data[0][3]
        elo = data[0][4]

        sql = "select count(pg2.pid), pg2.name, " \
              "SUM(case when pg.GF < pg.GA THEN 1 WHEN pg.GF > pg.GA THEN 0 end), \
(SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
from playergames pg  left join playergames as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 asc LIMIT 5 "

        c.execute(sql, [t1])
        data = c.fetchall()
        if(len(data) > 0):
            strMessage += "Worst Team Mates for **" + name + "** (5 games minimum):\n"
            first = True
            for game in data:
                if first:
                    first = False
                else:
                  strMessage += "\n"
                strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"


        await ctx.send(strMessage)

        conn.commit()
    except: 

        try:
            conn = sqlite3.connect(db_path)
            strMessage = ""
            c = conn.cursor()

            if(p1 == ""):
                p1 = ctx.message.author.id

            t1 = ctx.author.id

            if t1 is None:
                await ctx.send("No user found by the name \"" + p1 + "\"!")
                conn.commit()
                return

            sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
    AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
    and (GF + GA != 0 ) "

            c.execute(sql, [t1])
            data = c.fetchall()
            GF = data[0][0]
            GA = data[0][1]
            PlusMinus = data[0][2]
            name = data[0][3]
            elo = data[0][4]

            sql = "select count(pg2.pid), pg2.name, " \
                "SUM(case when pg.GF < pg.GA THEN 1 WHEN pg.GF > pg.GA THEN 0 end), \
    (SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
    from playergames pg  left join playergames as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
    where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
    ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 asc LIMIT 5 "

            c.execute(sql, [t1])
            data = c.fetchall()
            if(len(data) > 0):
                strMessage += "Worst Team Mates for **" + name + "** (5 games minimum):\n"
                first = True
                for game in data:
                    if first:
                        first = False
                    else:
                        strMessage += "\n"
                    strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"


            await ctx.send(strMessage)

            conn.commit()
        except Exception as e:
            exc_type, exc_obj, exc_tb = sys.exc_info()
            logger.error(str(exc_type) + "\n\n" + str(exc_obj) + "\n\n" + "Line: " + str(exc_tb.tb_lineno))

@client.command()
@commands.cooldown(1,2,commands.BucketType.user)
async def best(ctx, p1=None):
    """ Display Users Personal Stats. """

    if ctx.channel.id == ones_channel.id:

        try:
            conn = sqlite3.connect(db_path)
            strMessage = ""
            c = conn.cursor()

            if(p1 == ""):
                p1 = ctx.message.author.id

            t1 = find_userid_by_name(ctx, p1)

            if t1 is None:
                await ctx.send("No user found by the name \"" + p1 + "\"!")
                conn.commit()
                return

            sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
    AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
    and (GF + GA != 0 ) "

            c.execute(sql, [t1])
            data = c.fetchall()
            GF = data[0][0]
            GA = data[0][1]
            PlusMinus = data[0][2]
            name = data[0][3]
            elo = data[0][4]

            sql = "select count(pg2.pid), pg2.name, " \
                "SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end), \
    (SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
    from playergames pg  left join playergames as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
    where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
    ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 desc LIMIT 5 "


            c.execute(sql, [t1])
            data = c.fetchall()
            msg = ""
            if len(data)>0:
                strMessage += "\n\nBest Team Mates for **" + name + "** (5 games minimum):\n"
                first = True
                for game in data:
                    if first:
                        first = False
                    else:
                        strMessage += "\n"
                        strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"

            await ctx.send(strMessage)

            conn.commit()
        except: 

            try:
                conn = sqlite3.connect(db_path)
                strMessage = ""
                c = conn.cursor()

                if(p1 == ""):
                    p1 = ctx.message.author.id

                t1 = ctx.author.id

                if t1 is None:
                    await ctx.send("No user found by the name \"" + p1 + "\"!")
                    conn.commit()
                    return

                sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
        AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames where pID = ?  \
        and (GF + GA != 0 ) "

                c.execute(sql, [t1])
                data = c.fetchall()
                GF = data[0][0]
                GA = data[0][1]
                PlusMinus = data[0][2]
                name = data[0][3]
                elo = data[0][4]

                sql = "select count(pg2.pid), pg2.name, " \
                    "SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end), \
        (SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
        from playergames pg  left join playergames as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
        where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
        ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 desc LIMIT 5 "


                c.execute(sql, [t1])
                data = c.fetchall()
                msg = ""
                if len(data)>0:
                    strMessage += "\n\nBest Team Mates for **" + name + "** (5 games minimum):\n"
                    first = True
                    for game in data:
                        if first:
                            first = False
                        else:
                            strMessage += "\n"
                            strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"

                await ctx.send(strMessage)

                conn.commit()
            except Exception as e:
                exc_type, exc_obj, exc_tb = sys.exc_info()
                logger.error(str(exc_type) + "\n\n" + str(exc_obj) + "\n\n" + "Line: " + str(exc_tb.tb_lineno))

    if ctx.channel.id == twos_channel.id or ctx.channel.id == threes_channel.id:

        try:
            conn = sqlite3.connect(db_path)
            strMessage = ""
            c = conn.cursor()

            if(p1 == ""):
                p1 = ctx.message.author.id

            t1 = find_userid_by_name(ctx, p1)

            if t1 is None:
                await ctx.send("No user found by the name \"" + p1 + "\"!")
                conn.commit()
                return

            sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
    AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames_team where pID = ?  \
    and (GF + GA != 0 ) "

            c.execute(sql, [t1])
            data = c.fetchall()
            GF = data[0][0]
            GA = data[0][1]
            PlusMinus = data[0][2]
            name = data[0][3]
            elo = data[0][4]

            sql = "select count(pg2.pid), pg2.name, " \
                "SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end), \
    (SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
    from playergames_team pg  left join playergames_team as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
    where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
    ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 desc LIMIT 5 "


            c.execute(sql, [t1])
            data = c.fetchall()
            msg = ""
            if len(data)>0:
                strMessage += "\n\nBest Team Mates for **" + name + "** (5 games minimum):\n"
                first = True
                for game in data:
                    if first:
                        first = False
                    else:
                        strMessage += "\n"
                        strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"

            await ctx.send(strMessage)

            conn.commit()
        except: 

            try:
                conn = sqlite3.connect(db_path)
                strMessage = ""
                c = conn.cursor()

                if(p1 == ""):
                    p1 = ctx.message.author.id

                t1 = ctx.author.id

                if t1 is None:
                    await ctx.send("No user found by the name \"" + p1 + "\"!")
                    conn.commit()
                    return

                sql = "select AVG(GF) as 'Average Goals For',AVG(GA) as 'Average Goals Against',  \
        AVG(GF) - AVG(GA) as '+- Goals', name, elo from playergames_team where pID = ?  \
        and (GF + GA != 0 ) "

                c.execute(sql, [t1])
                data = c.fetchall()
                GF = data[0][0]
                GA = data[0][1]
                PlusMinus = data[0][2]
                name = data[0][3]
                elo = data[0][4]

                sql = "select count(pg2.pid), pg2.name, " \
                    "SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end), \
        (SUM(case when pg.GF > pg.GA THEN 1 WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 as 'Win Percent' \
        from playergames_team pg  left join playergames_team as pg2 on pg2.ID = pg.ID and pg2.teamID = pg.teamID and pg2.pid != pg.pid \
        where pg.pID  = ? and (pg.GF + pg.GA != 0 ) group by PG2.pid, pg2.name having count(pg2.pid) >= 5 \
        ORDER BY (SUM(case  when pg.GF > pg.GA THEN 1  WHEN pg.GF < pg.GA THEN 0 end) * 1.0000) / (count(pg2.pid) * 1.0000) * 100 desc LIMIT 5 "


                c.execute(sql, [t1])
                data = c.fetchall()
                msg = ""
                if len(data)>0:
                    strMessage += "\n\nBest Team Mates for **" + name + "** (5 games minimum):\n"
                    first = True
                    for game in data:
                        if first:
                            first = False
                        else:
                            strMessage += "\n"
                        strMessage += game[1] + " (" + str(round(game[3], 2)) + "%)"

                await ctx.send(strMessage)

                conn.commit()
            except Exception as e:
                exc_type, exc_obj, exc_tb = sys.exc_info()
                logger.error(str(exc_type) + "\n\n" + str(exc_obj) + "\n\n" + "Line: " + str(exc_tb.tb_lineno))



@client.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def noscore(ctx):

    global no_score

    conn = sqlite3.connect(db_path)
    c = conn.cursor()

    for game_id in c.execute("SELECT MAX(ID) FROM GAMES"):
        game_ID = (game_id[0])
        
    await ctx.send("**Game #" + str(game_ID) + "**: " + ', '.join(no_score))


@client.command()
async def signup(ctx):

    """Tournament signups."""

    t = ctx.author.id
    name = ctx.author.name
    date = datetime.datetime.now()
    conn = sqlite3.connect(db_path)
    c = conn.cursor()
    try:

        c.execute("SELECT name FROM tournament WHERE ID = ?", [t])
        row = c.fetchone()[0]

    except:
            
        await ctx.send("What position would you like to play? (Options: GoalKeeper, Defense, Offense, Mobility)")

        def check(message):
            return message.channel == ctx.channel and message.author.id == int(t)

        try:

            message = await client.wait_for('message', timeout=30, check=check)

            position = message.content
            print(position)

            c.execute("INSERT INTO tournament VALUES (?,?,?,?)", [t,name,position,date])
            conn.commit()
            conn.close()

            await ctx.send(f"You are now signed up as **{name}** and the position you applied for was **{position}**!")

        except asyncio.TimeoutError:

            error_msg2 = await ctx.send("Oops! Too late.")
            await error_msg2.edit(delete_after=5)
            return

    else:

        await ctx.send("You have already signed up!")

@client.command()
async def members(ctx):

    guild = ctx.guild
    for member in guild.members:
        print(member)

record_pattern = re.compile(".*\[.*\].*\[.*\].*\[.*\].*", flags=re.IGNORECASE)

@client.command()
@commands.has_any_role("League Admin")
async def record_legacy(ctx, *args):
    record_info = " ".join(args)
    # !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] 
    if not record_pattern.match(record_info):
        print("regex matching failed")
        await ctx.send("Invalid command. Command should look like this (capitalization included): \n !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2]")
        # print fail, give !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] as working example
        return
    
    team1_start = record_info.find("[")
    team1_end = record_info.find("]", team1_start) + 1
    team1_str = record_info[team1_start:team1_end]

    team2_start = record_info.find("[", team1_end)
    team2_end = record_info.find("]", team2_start) + 1
    team2_str = record_info[team2_start:team2_end]

    result_start = record_info.find("[", team2_end)
    result_end = record_info.find("]", result_start) + 1
    results = [int(k) for k in eval(record_info[result_start:result_end])]

    if np.any([np.any([np.array(results) > 2]), np.any(np.array(results) < 1)]):
        await ctx.send("Results should only contains 1s and 2s representing wins for each respective team.")
        # print fail, results is a list showing the order of wins for each team (for example, [1,2,1] means team 1 won, then team 2 won then team 1 won again)
        return

    ids = []
    i = 0
    team1 = []
    while i < len(team1_str):
        c = team1_str[i]
        if c == "<":
            player_id = ""
            i += 3 # <@!361548991755976704>
            c = team1_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team1_str[i]
            team1.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team1) == 0:
        # print fail, team 1 empty
        await ctx.send("Team 1 empty.")
        return

    i = 0
    team2 = []
    while i < len(team2_str):
        c = team2_str[i]
        if c == "<":
            player_id = ""
            i += 3
            c = team2_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team2_str[i]
            team2.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team2) == 0:
        await ctx.send("Team 2 empty.")
        # print fail, team 2 empty
        return
    
    if len(team1) != len(team2):
        # print unbalanced teams
        await ctx.send("Unbalanced teams.")
        return
        
    activity_channel = ctx.guild.get_channel(790313358816968715)
    conn = sqlite3.connect(db_path, uri=True)
    c = conn.cursor()
    auth = ctx.message.author.id

    games_table = "games"
    players_table = "players"

    if len(team1) > 1:
        games_table += "_team"
        players_table += "_team"

    c.execute(f"SELECT MAX(ID) from {games_table}")
    game_id = c.fetchone()[0]
    if game_id is None:
        game_id = 1
    else:
        game_id = int(game_id) + 1

    start = datetime.datetime.now()
    time = start.strftime("%M")
    time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")

    values = "?, " + "?, " * len(ids) + "NULL, " * (8 - len(ids)) + "?, ?, ?, NULL, ?"
    values1 = [str(p) for p in team1] + [str(p) for p in team2] + ["won", "lost"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]
    values2 = [str(p) for p in team1] + [str(p) for p in team2] + ["lost", "won"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]

    game_type = f"{len(team1)}v{len(team1)}"

    for result in results:
        
        if result == 1:
            c.execute(f"INSERT INTO {games_table} VALUES({values})", [str(game_id)] + values1)
            team_won = team1
            team_lost = team2
        else:
            c.execute(f"INSERT INTO {games_table} VALUES({values})", [str(game_id)] + values2)
            team_won = team2
            team_lost = team1

        team_won_ratings = []
        for t in team_won:
            c.execute(f"SELECT elo, sigma FROM {players_table} where ID = ?", [str(t)])
            row = c.fetchone()
            elo = row[0]
            sigma = row[1]
            team_won_ratings.append(trueskill.Rating(elo, sigma))
        
        team_lost_ratings = []
        for t in team_lost:
            c.execute(f"SELECT elo, sigma FROM {players_table} where ID = ?", [str(t)])
            row = c.fetchone()
            elo = row[0]
            sigma = row[1]
            team_lost_ratings.append(trueskill.Rating(elo, sigma))

        team_won_ratings, team_lost_ratings = trueskill.rate([team_won_ratings, team_lost_ratings])

        for i, t in enumerate(team_won):
            c.execute(f"UPDATE {players_table} SET win = win + 1 where ID = ?", [str(t)])
            c.execute(f"UPDATE {players_table} SET streak = streak + 1 WHERE ID = ?", [str(t)])
            c.execute(f"UPDATE {players_table} SET elo = ? where ID = ?", [team_won_ratings[i].mu, t])
            c.execute(f"UPDATE {players_table} SET sigma = ? where ID = ?", [team_won_ratings[i].sigma, t])

        for i, t in enumerate(team_lost):
            c.execute(f"UPDATE {players_table} SET loss = loss + 1 where ID = ?", [str(t)])
            c.execute(f"UPDATE {players_table} SET streak = 0 WHERE ID = ?", [str(t)])
            c.execute(f"UPDATE {players_table} SET elo = ? where ID = ?", [team_lost_ratings[i].mu, t])
            c.execute(f"UPDATE {players_table} SET sigma = ? where ID = ?", [team_lost_ratings[i].sigma, t])

        conn.commit()
        #conn.close()
        #del global_dict[game_id]

        await activity_channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")
        await ctx.channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")
        game_id += 1

    if len(team1) > 1:
        await leaderboard_team(ctx)
    else:
        await leaderboard_solo(ctx)
    
    conn.close()

record_pattern = re.compile(".*\[.*\].*\[.*\].*\[.*\].*", flags=re.IGNORECASE)

@client.command()
@commands.has_any_role("League Admin")
async def record(ctx, *args):
    record_info = " ".join(args)
    # !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] 
    if not record_pattern.match(record_info):
        print("regex matching failed")
        await ctx.send("Invalid command. Command should look like this (capitalization included): \n !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2]")
        # print fail, give !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] as working example
        return
    
    team1_start = record_info.find("[")
    team1_end = record_info.find("]", team1_start) + 1
    team1_str = record_info[team1_start:team1_end]

    team2_start = record_info.find("[", team1_end)
    team2_end = record_info.find("]", team2_start) + 1
    team2_str = record_info[team2_start:team2_end]

    result_start = record_info.find("[", team2_end)
    result_end = record_info.find("]", result_start) + 1
    results = [int(k) for k in eval(record_info[result_start:result_end])]

    if np.any([np.any([np.array(results) > 2]), np.any(np.array(results) < 1)]):
        await ctx.send("Results should only contains 1s and 2s representing wins for each respective team.")
        # print fail, results is a list showing the order of wins for each team (for example, [1,2,1] means team 1 won, then team 2 won then team 1 won again)
        return

    ids = []
    i = 0
    team1 = []
    while i < len(team1_str):
        c = team1_str[i]
        if c == "<":
            player_id = ""
            i += 3 # <@!361548991755976704>
            c = team1_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team1_str[i]
            team1.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team1) == 0:
        # print fail, team 1 empty
        await ctx.send("Team 1 empty.")
        return
    if len(team1) > 1:
        await ctx.send("Team 1 has too many players (there should only be 1).")
        return

    i = 0
    team2 = []
    while i < len(team2_str):
        c = team2_str[i]
        if c == "<":
            player_id = ""
            i += 3
            c = team2_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team2_str[i]
            team2.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team2) == 0:
        await ctx.send("Team 2 empty.")
        # print fail, team 2 empty
        return
    if len(team1) > 1:
        await ctx.send("Team 2 has too many players (there should only be 1).")
        return

    activity_channel = ctx.guild.get_channel(790313358816968715)
    conn = sqlite3.connect(db_path, uri=True)
    c = conn.cursor()
    auth = ctx.message.author.id

    games_table = "games"
    players_table = "players"

    player1 = team1[0]
    player2 = team2[0]

    c.execute(f"SELECT MAX(ID) from {games_table}")
    game_id = c.fetchone()[0]
    if game_id is None:
        game_id = 1
    else:
        game_id = int(game_id) + 1

    start = datetime.datetime.now()
    time = start.strftime("%M")
    time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")

    values = "?, " + "?, " * len(ids) + "NULL, " * (8 - len(ids)) + "?, ?, ?, NULL, ?"
    values1 = [str(p) for p in team1] + [str(p) for p in team2] + ["won", "lost"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]
    values2 = [str(p) for p in team1] + [str(p) for p in team2] + ["lost", "won"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]

    game_type = f"{len(team1)}v{len(team1)}"

    for result in results:
        
        if result == 1:
            c.execute(f"INSERT INTO {games_table} VALUES({values})", [str(game_id)] + values1)
            player_won = player1
            player_lost = player2
        else:
            c.execute(f"INSERT INTO {games_table} VALUES({values})", [str(game_id)] + values2)
            player_won = player2
            player_lost = player1
        

        c.execute(f"SELECT elo, sigma, win, loss FROM {players_table} where ID = ?", [str(player_won)])
        row = c.fetchone()
        elo1 = row[0]
        sigma1 = row[1]
        total_games1 = row[2] + row[3]

        c.execute(f"SELECT elo, sigma, win, loss FROM {players_table} where ID = ?", [str(player_lost)])
        row = c.fetchone()
        elo2 = row[0]
        sigma2 = row[1]
        total_games2 = row[2] + row[3]


        if (total_games1 < 20 and total_games2 < 20) or (total_games1 >= 20 and total_games2 >= 20):
            player_won_rating, player_lost_rating = trueskill.rate_1vs1(trueskill.Rating(elo1, sigma1), trueskill.Rating(elo2, sigma2))
            elo1 = player_won_rating.mu
            sigma1 = player_won_rating.sigma
            elo2 = player_lost_rating.mu
            sigma2 = player_lost_rating.sigma
        elif total_games1 < 20:
            player_won_rating, player_lost_rating = trueskill.rate_1vs1(trueskill.Rating(elo1, sigma1), trueskill.Rating(elo2, 30))
            elo1 = player_won_rating.mu
            sigma1 = player_won_rating.sigma
            elo2 = player_lost_rating.mu
        else:
            player_won_rating, player_lost_rating = trueskill.rate_1vs1(trueskill.Rating(elo1, 30), trueskill.Rating(elo2, sigma2))
            elo1 = player_won_rating.mu
            elo2 = player_lost_rating.mu
            sigma2 = player_lost_rating.sigma


        c.execute(f"UPDATE {players_table} SET win = win + 1 where ID = ?", [str(player_won)])
        c.execute(f"UPDATE {players_table} SET streak = streak + 1 WHERE ID = ?", [str(player_won)])
        c.execute(f"UPDATE {players_table} SET elo = ? where ID = ?", [elo1, str(player_won)])
        c.execute(f"UPDATE {players_table} SET sigma = ? where ID = ?", [sigma1, str(player_won)])

        c.execute(f"UPDATE {players_table} SET loss = loss + 1 where ID = ?", [str(player_lost)])
        c.execute(f"UPDATE {players_table} SET streak = 0 WHERE ID = ?", [str(player_lost)])
        c.execute(f"UPDATE {players_table} SET elo = ? where ID = ?", [elo2, str(player_lost)])
        c.execute(f"UPDATE {players_table} SET sigma = ? where ID = ?", [sigma2, str(player_lost)])

        conn.commit()
        #conn.close()
        #del global_dict[game_id]

        await activity_channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")
        await ctx.channel.send(f"[{game_type}] Game #" + str(game_id) + " has finished.")
        game_id += 1

    await leaderboard_solo(ctx)
    
    conn.close()

@client.command()
async def simulate(ctx, *args):
    record_info = " ".join(args)
    # !simulate Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] 
    if not record_pattern.match(record_info):
        print("regex matching failed")
        await ctx.send("Invalid command. Command should look like this (capitalization included): \n !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2]")
        # print fail, give !record Team1 - [@player1, @player2], Team2 - [@player3, @player4], Results - [1,2,1,2,2,2] as working example
        return
    
    team_won_ratings = []
    team_lost_ratings = []
    team1_start = record_info.find("[")
    team1_end = record_info.find("]", team1_start) + 1
    team1_str = record_info[team1_start:team1_end]

    team2_start = record_info.find("[", team1_end)
    team2_end = record_info.find("]", team2_start) + 1
    team2_str = record_info[team2_start:team2_end]

    result_start = record_info.find("[", team2_end)
    result_end = record_info.find("]", result_start) + 1
    results = [int(k) for k in eval(record_info[result_start:result_end])]

    if np.any([np.any([np.array(results) > 2]), np.any(np.array(results) < 1)]):
        await ctx.send("Results should only contains 1s and 2s representing wins for each respective team.")
        # print fail, results is a list showing the order of wins for each team (for example, [1,2,1] means team 1 won, then team 2 won then team 1 won again)
        return

    ids = []
    i = 0
    team1 = []
    while i < len(team1_str):
        c = team1_str[i]
        if c == "<":
            player_id = ""
            i += 3 # <@!361548991755976704>
            c = team1_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team1_str[i]
            team1.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team1) == 0:
        # print fail, team 1 empty
        await ctx.send("Team 1 empty.")
        return

    i = 0
    team2 = []
    while i < len(team2_str):
        c = team2_str[i]
        if c == "<":
            player_id = ""
            i += 3
            c = team2_str[i]
            while c != ">":
                player_id += c
                i += 1
                c = team2_str[i]
            team2.append(int(player_id))
            ids.append(int(player_id))
        i += 1
    if len(team2) == 0:
        await ctx.send("Team 2 empty.")
        # print fail, team 2 empty
        return
    
    if len(team1) != len(team2):
        # print unbalanced teams
        await ctx.send("Unbalanced teams.")
        return
        
    activity_channel = ctx.guild.get_channel(790313358816968715)
    conn = sqlite3.connect(db_path, uri=True)
    c = conn.cursor()
    auth = ctx.message.author.id

    games_table = "games"
    players_table = "players"

    if len(team1) > 1:
        games_table += "_team"
        players_table += "_team"

    c.execute(f"SELECT MAX(ID) from {games_table}")
    game_id = c.fetchone()[0]
    if game_id is None:
        game_id = 1
    else:
        game_id = int(game_id) + 1

    start = datetime.datetime.now()
    time = start.strftime("%M")
    time_data2 = start.strftime("%B"),start.strftime("%d") + ", " + start.strftime("%Y"), start.strftime("%I") + ":" + start.strftime("%M") + " " + start.strftime("%p")

    values = "?, " + "?, " * len(ids) + "NULL, " * (8 - len(ids)) + "?, ?, ?, NULL, ?"
    values1 = [str(p) for p in team1] + [str(p) for p in team2] + ["won", "lost"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]
    values2 = [str(p) for p in team1] + [str(p) for p in team2] + ["lost", "won"] + [int(time)] + [time_data2[0] + " " + time_data2[1] + " " + time_data2[2]]

    game_type = f"{len(team1)}v{len(team1)}"

    team_won_ratings = []
    for t in team1:
        c.execute(f"SELECT elo, sigma FROM {players_table} where ID = ?", [str(t)])
        row = c.fetchone()
        elo = row[0]
        sigma = row[1]
        team_won_ratings.append(trueskill.Rating(elo, sigma))
    
    team_lost_ratings = []
    for t in team2:
        c.execute(f"SELECT elo, sigma FROM {players_table} where ID = ?", [str(t)])
        row = c.fetchone()
        elo = row[0]
        sigma = row[1]
        team_lost_ratings.append(trueskill.Rating(elo, sigma))

    last_result = 1
    for result in results:
        
        if result != last_result:
            last_result = result
            team_won_ratings, team_lost_ratings = team_lost_ratings, team_won_ratings

        team_won_ratings, team_lost_ratings = trueskill.rate([team_won_ratings, team_lost_ratings])

    if last_result != 1:
        team_won_ratings, team_lost_ratings = team_lost_ratings, team_won_ratings
    
    s = "Simulated Elos:\n"
    for i, t in enumerate(team1):
        s += f"<@!{t}>: {team_won_ratings[i].mu:.2f}\n"
    for i, t in enumerate(team2):
        s += f"<@!{t}>: {team_lost_ratings[i].mu:.2f}\n"

    await ctx.send(s)

    conn.close()
    
client.run("Nzg1MDA4MzE2ODgzNDAyNzc0.X8xl9w.woujElelGS5EGInzerRzZOIPSmc")  # client auth key (found in discord api)
