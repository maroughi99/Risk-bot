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
async def members(ctx):

    guild = ctx.guild
    for member in guild.members:
        print(member)

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