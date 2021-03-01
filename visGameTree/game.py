#!/usr/bin/env python

## GUI Toolkit
from tkinter import *
import tkinter.font as tkFont 
from tkinter import messagebox
#import tkFont 
import random
import math
import copy
import networkx as nx
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import graphviz_layout
from matplotlib.animation import FuncAnimation
from copy import deepcopy
import functools 
cache = functools.lru_cache(10**6)

global visits_times
#global board_vis
global last_iteration

global forest_steps
global root_node
global di
global factor_input
global iteration_count 
global play_iteration
global tutorial_iteration
dx = [ 1, 1,  1,  0 ]
dy = [ 1, 0,  -1,  1  ]
#tree_frames Monto Carlo 
#mode: play/tutorial
#tree for minimax based algorithm 
#evaluation: simple, complex
#show_utilites

# play mode and tutorial mode
## Game basic dynamics
class Board(object):
    
    def __init__(self, board , last_move = [ None , None ] ):
        self.board = board 
        self.last_move = last_move
        self.utility = 0
    
    def __str__(self):
        output = ''
        for row in range(6):
            for col in range(7):
                content = self.board[row][col]
                if (col < 6):
                    output += '{}'.format(content)
                else:
                    output += '{}\n'.format(content)
        output = output.replace('0', '~')
        output = output.replace('-1','Y')
        output = output.replace('1','R')
        return output 

    def tryMove(self, move):
        # Takes the current board and a possible move specified 
        # by the column. Returns the appropriate row where the 
        # piece be located. If it's not found it returns -1.

        if ( move < 0 or move > 7 or self.board[0][move] != 0 ):
            return -1 ;

        for i in range(len(self.board)):
            if ( self.board[i][move] != 0 ):
                return i-1
        return len(self.board)-1

    def terminal(self):
       # Returns true when the game is finished, otherwise false.
        for i in range(len(self.board[0])):
               if ( self.board[0][i] == 0 ):
                   return False
        return True

    def legal_moves(self):
        # Returns the full list of legal moves that for next player.
        legal = []
        for i in range(len(self.board[0])):
            if( self.board[0][i] == 0 ):
                legal.append(i)

        return legal
    
    def next_state(self, turn):
        # Retuns next state
        aux = copy.deepcopy(self)
        moves = aux.legal_moves()
        #take a random column to move
        if len(moves) > 0 :
            ind = random.randint(0,len(moves)-1)
            row = aux.tryMove(moves[ind])
            aux.board[row][moves[ind]] = turn
            aux.last_move = [ row, moves[ind] ]
            
        return aux 

    def move_by_index(self, col, turn):
        aux = copy.deepcopy(self)

        row = aux.tryMove(col)
        aux.board[row][col] = turn
        aux.last_move = [ row, col]

        aux.utility += aux.winner() 
        return aux 
    
    def move(self, col, turn):
        aux = copy.deepcopy(self)

        row = aux.tryMove(col)
        aux.board[row][col] = turn
        aux.last_move = [ row, col]
        return aux 
    def winner(self):
        # Takes the board as input and determines if there is a winner.
        # If the game has a winner, it returns the player number (Computer = 1, Human = -1).
        # If the game is still ongoing, it returns zero.  

        x = self.last_move[0]
        y = self.last_move[1]

        if x == None:
            return 0 

        for d in range(4):

            h_counter = 0
            c_counter = 0

            for k in range(-3,4):

                u = x + k * dx[d]
                v = y + k * dy[d]

                if u < 0 or u >= 6:
                    continue

                if v < 0 or v >= 7:
                    continue

                if self.board[u][v] == -1:
                    c_counter = 0
                    h_counter += 1
                elif self.board[u][v] == 1:
                    h_counter = 0
                    c_counter += 1
                else:
                    h_counter = 0
                    c_counter = 0

                if h_counter == 4:
                    return -1 

                if c_counter == 4:    
                    return 1

        return 0


## Monte Carlo Tree Search

class Node():
# Data structure to keep track of game tree search
    def __init__(self, state, parent = None):
        self.visits = 0
        self.reward = 0.0
        self.state = state
        self.children = []
        self.children_move = []
        self.parent = parent 

    def addChild( self , child_state , move=None ):
        child = Node(child_state,self)
        child.parent = self
        self.children.append(child)
        self.children_move.append(move)

    def update( self,reward ):
        self.reward += reward 
        self.visits += 1

    def fully_explored(self):
        if len(self.children) == len(self.state.legal_moves()):
            return True
        return False
    def __str__(self):
        return str(self.state) + '\nR:' + str(self.reward) + '\nV:' +str(self.visits)

class NodeGUI():
    def __init__(self, stage, tree_dic, inter):
        self.tree_dic = tree_dic
        self.stage = stage
        self.iteration = inter
        self.add_edges = []
    def __str__(self):
        return str(self.tree_dic) + self.stage + '\n'
    def add(self, edge):
        self.add_edges.append(edge)

class MiniNode():
    def __init__(self,  state):

        self.next = []
        self.state = state
        self.utility = 0
        self.alpha = "-infinite"
        self.beta = "+finite"
    def __str__(self):
        global evaluation
        global algorithm

        if evaluation == "Simple evaluation":
            if algorithm == "alphabeta":
                return str(self.state) + '\nUtility: ' + str(self.state.utility) + " alpha: " + self.alpha + " beta: " + self.beta
            return str(self.state) + '\nUtility: ' + str(self.state.utility)
        if algorithm == "alphabeta":
            return str(self.state) + '\nUtility: ' + str(self.utility) + " alpha: " + self.alpha + " beta: " + self.beta
        return str(self.state) + '\nUtility: ' + str(self.utility)
#check if the state has a connect four 
    # return: 276 if current player has connect4, 
    #         0 if no connect4,
    #         -276 if opponent has connect4
def connect_four(board):
    connect_four = False
    board = board.board
    for i in range(len(board)):
        #print("i: ")
        #print(i)
        if i < len(board) - 3:
            for j in range(len(board[0])):
                check = connect_four_for_position(board, i, j)
                if check != 0:
                    return check
        else:
            for j in range(len(board[0])- 3):
                check = connect_four_for_position(board, i, j)
                if check != 0:
                    return check
    return 0

def connect_four_for_position(board, row, col):
    connect_four = False
    #check if connect 4 from current position down
    if row < len(board) - 3:
        #check for current player
        curr_player = True
        #check for opponent
        opponent = True
        for r in range(4):
            if (board[row + r][col] != 1): #1 is computer
                curr_player = False
            if (board[row + r][col] == 1 or board[row + r][col] == 0):
                opponent = False
        
        if (curr_player):
            return 1000
        if (opponent):
            return -1000

        #check diagonal if connect 4 from current position down and to right 
        if col < len(board[0]) - 3:
            #check for current player
            curr_player = True
            #check for opponent
            opponent = True
            for r in range(4):
                if (board[row + r][col + r] != 1):
                    curr_player = False
                if (board[row + r][col + r] == 1 or board[row + r][col + r] == 0):
                    opponent = False
            
            if (curr_player):
                return 1000
            if (opponent):
                return -1000

    #check if connect 4 from current position to right 
    if col < len(board[0]) - 3:
        #check for current player
        curr_player = True
        #check for opponent
        opponent = True
        for r in range(4):
            if (board[row][col + r] != 1):
                curr_player = False
            if (board[row][col + r] == 1 or board[row][col + r] == 0):
                opponent = False
        if (curr_player):
            return 1000
        if (opponent):
            return -1000
        #check diagonal if connect 4 from current position up and to right 
        if row > 2:
            #check for current player
            curr_player = True
            #check for opponent
            opponent = True
            for r in range(4):
                if (board[row - r][col + r] != 1):
                    curr_player = False
                if (board[row - r][col + r] == 1 or board[row - r][col + r] == 0):
                    opponent = False
            if (curr_player):
                return 1000
            if (opponent):
                return -1000

    return 0
def evaluation_function(board):
    evaluationValue = [[3, 4, 5, 7, 5, 4, 3],    
                       [4, 6, 8, 10, 8, 6, 4], 
                       [5, 8, 11, 13, 11, 8, 5], 
                       [5, 8, 11, 13, 11, 8, 5],
                       [4, 6, 8, 10, 8, 6, 4],   
                       [3, 4, 5, 7, 5, 4, 3]]
    # Initial each state; the range of untility is between -138 to 138 
    util = 0;
    #block opponent/connect 4 for current player
    check = connect_four(board)
    if check != 0:
        return check

    board = board.board
    for row in range(len(board)):
        for col in range(len(board[0])):
            if board[row][col] == 1: #computer's chess
                util += evaluationValue[row][col]
            elif board[row][col] != 0:
                util -= evaluationValue[row][col]

    return util 

def MiniMax(root):
    global tree
    global depth

    tree = []

    #root is Board
    turn = 1 #begin from computer's move

    vis_node = MiniNode(root)
    dummy = MiniNode(None)
    dummy.next.append(vis_node)
    @cache
    def max_value(state, turn, vis, dep):
        global evaluation
        global show_utilites
        global depth
        global mode

        if state.winner() != 0:
            if evaluation == "Simple evaluation":
                return state.winner(), None
            return evaluation_function(state), None
        if state.terminal() or dep == 0:
            #return evaluation
            if evaluation == "Simple evaluation":

                return state.utility, None
            return evaluation_function(state), None
        v, move = float('-inf'), []

        for ac in state.legal_moves():
            
            new_state = state.move_by_index(ac, turn)
            if (mode != "play"):
                new_node = MiniNode(new_state)
                vis.next.append(new_node)
                tree.append(deepcopy(dummy.next[0]))
                v2, t = min_value(new_state, -turn, new_node, dep-1)
            else:
                v2, t = min_value(new_state, -turn, None, dep-1)
            if v2 > v:
                v, move = v2, [ac]
            if v2 == v:
                move.append(ac)
            if dep == depth:
                show_utilites[ac] = v2
            #node_rep = str(new_state) + "\n" + "utility: " + v2
            
            if (mode != "play"):
                new_node.utility = v2
                tree.append(deepcopy(dummy.next[0]))
            
        if len(move) == 0:
            move = None
        else:
            move = random.choice(move)

        return v, move
    @cache
    def min_value(state, turn, vis, dep):
        global evaluation
        global mode
        if state.winner() != 0:
            if evaluation == "Simple evaluation":
                return state.winner(), None
            return evaluation_function(state), None
        if state.terminal() or dep == 0:
            #return evaluation
            if evaluation == "Simple evaluation":
                return state.utility, None
            return evaluation_function(state), None
        v, move = float('inf'), []

        for ac in state.legal_moves():
            new_state = state.move_by_index(ac, turn)
            if (mode != "play"):
                new_node = MiniNode(new_state)
                vis.next.append(new_node)
                tree.append(deepcopy(dummy.next[0]))
                v2, t = max_value(new_state, -turn, new_node, dep-1)
            else:
                v2, t = max_value(new_state, -turn, None, dep-1)
            if v2 < v:
                v, move = v2, [ac]
            if v2 == v:
                move.append(ac)
            if (mode != "play"):
                new_node.utility = v2
                tree.append(deepcopy(dummy.next[0]))

        if len(move) == 0:
            move = None
        else:
            move = random.choice(move)
        return v, move

    v, move = max_value(root, turn, vis_node, depth)
    vis_node.utility = v
    return root.move(move, 1)
def random_player(root):
    moves = root.legal_moves()
    if len(moves) == 0:
        return None
    return random.choice(moves)


def alpha_beta_search(root):
    global tree
    global depth

    tree = []

    turn = 1 #begin from computer's move
    #next_state = root.next_state(1)
    count = 0
    vis_node = MiniNode(root)
    dummy = MiniNode(None)
    dummy.next.append(vis_node)
    @cache
    def max_value(state, turn, vis, dep, alpha, beta):
        global evaluation
        global show_utilites
        global depth
        global mode
        if state.winner() != 0:
            if evaluation == "Simple evaluation":
                return state.winner(), None
            return evaluation_function(state), None
        if state.terminal() or dep == 0:
            #return evaluation
            if evaluation == "Simple evaluation":
                return state.utility, None
            return evaluation_function(state), None
        v, move = float('-inf'), []

        for ac in state.legal_moves():
            
            new_state = state.move_by_index(ac, turn)
            if (mode != "play"):
                new_node = MiniNode(new_state)
                vis.next.append(new_node)
                tree.append(deepcopy(dummy.next[0]))
                v2, t = min_value(new_state, -turn, new_node, dep-1, alpha, beta)
            else:
                v2, t = min_value(new_state, -turn, None, dep-1, alpha, beta)
            if v2 > v:
                v, move = v2, [ac]
                alpha = max(alpha, v)
                if (mode != "play"):
                    new_node.alpha = str(alpha)
            if v2 == v:
                move.append(ac)
            if dep == depth:
                show_utilites[ac] = v2
            if (mode != "play"):
                new_node.utility = v2
                tree.append(deepcopy(dummy.next[0]))
            if v >= beta:
                return v, move
            #node_rep = str(new_state) + "\n" + "utility: " + v2
        if len(move) == 0:
            move = None
        else:
            move = random.choice(move)
        return v, move
    @cache
    def min_value(state, turn, vis, dep, alpha, beta):
        global mode
        global evaluation

        if state.winner() != 0:
            if evaluation == "Simple evaluation":
                return state.winner(), None

            return evaluation_function(state), None
        if state.terminal() or dep == 0:
            #return evaluation
            if evaluation == "Simple evaluation":
                return state.utility, None
            return evaluation_function(state), None
        v, move = float('inf'), []

        for ac in state.legal_moves():
            new_state = state.move_by_index(ac, turn)
            if (mode != "play"):
                new_node = MiniNode(new_state)
                vis.next.append(new_node)
                tree.append(deepcopy(dummy.next[0]))
                v2, t = max_value(new_state, -turn, new_node, dep-1, alpha, beta)
            else:
                v2, t = max_value(new_state, -turn, None, dep-1, alpha, beta)
            if v2 < v:
                v, move = v2, [ac]
                beta = min(beta, v)
                if (mode != "play"):
                    new_node.beta = str(beta)
            if v2 == v:
                move.append(ac)
            if (mode != "play"):
                new_node.utility = v2
                tree.append(deepcopy(dummy.next[0]))
            if v <= alpha:
                return v, move
        if len(move) == 0:
            move = None
        else:
            move = random.choice(move)

        return v, move

    v, move = max_value(root, turn, vis_node, depth, float('-inf'), float('inf'))
    vis_node.utility = v
    return root.move(move, 1)

def MTCS( maxIter , root , factor ):

    global last_iteration
    global forest_steps
    global tree_frames
    global root_node
    global mode
    root_node = root
    tree_frames = []
    
    for inter in range(maxIter):
        front, turn = treePolicy(root , 1 , factor, inter)
        reward = defaultPolicy(front, turn, inter)
        backup(front,reward,turn, inter)

    ans = bestChild(root,0, True)

    if (mode == "play"):
        return ans
    
    tree_d = {}
    transformation(root_node, tree_d)
    n = NodeGUI("End", tree_d,inter)
    tree_frames.append(n)
    
    return ans



def treePolicy( node, turn , factor, inter, max_ite = False):

   
    while node.state.terminal() == False and node.state.winner() == 0:
        if ( node.fully_explored() == False ):
            front = expand(node, turn)
            if (mode == "play"):
                return front, -turn
            tree_d = {}
            transformation(root_node, tree_d)
            n = NodeGUI("expanding", tree_d, inter)
            tree_frames.append(n)
            return front, -turn
        else:
            node = bestChild ( node , factor)
            turn *= -1
            if (mode != "play"):
                tree_d = {}
                transformation(root_node, tree_d)
                n = NodeGUI("selection", tree_d, inter)
                tree_frames.append(n)
    return node, turn

def expand( node, turn ):
    tried_children_move = [m for m in node.children_move]
    possible_moves = node.state.legal_moves()
    #new_state = copy.deepcopy(node.state)
    #con = False
    for move in possible_moves:
        if move not in tried_children_move:
            row = node.state.tryMove(move)
            new_state = copy.deepcopy(node.state)
            new_state.board[row][move] = turn 
            new_state.last_move = [ row , move ]
            #con = True
            break
    #if (con):
        #n = Node(new_state)
    node.addChild(new_state,move)
    return node.children[-1]

#Node maximizing UCT is the one to follow
#factor in the UCT formula controls the trade-off between exploitation and exploration in Monte Carlo Tree Search.
def bestChild(node,factor, best = False, ite = None):
    bestscore = -10000000.0
    bestChildren = []
    global show_utilites
    index = 0
    for c in node.children:
        # UCT (Upper Confidence Bound applied to trees)
        #wining/losing rate: the number of wins over the total number of rollouts that have been through that node
        exploit = c.reward / c.visits
        explore = math.sqrt(math.log(2.0*node.visits)/float(c.visits))
        score = exploit + factor*explore
        if score == bestscore:
            bestChildren.append(c)
        if score > bestscore:
            bestChildren = [c]
            bestscore = score 
        show_utilites[node.children_move[index]] = round(score,2)

        index += 1
    return random.choice(bestChildren)

#randomly choose next step, loop until terminal or get a winner
def defaultPolicy( choice, turn, inter, max_ite = False ):
    state = choice.state
    tree_d = {}
    transformation(root_node, tree_d)
    n = NodeGUI("simulating", tree_d, inter)
    pre = str(choice.state) + '\nR:' + str(choice.reward) + '\nV:' +str(choice.visits)
    
    while state.terminal()==False and state.winner() == 0 :
        state = state.next_state( turn )
        turn *= -1
        if (mode != "play"):
            curr = str(state) + '\nR:' +str(state.winner())
            edge = (pre, curr)
            n = deepcopy(n)
            n.add(edge)
            pre = curr
            tree_frames.append(n)
    
    return state.winner() 

def backup( node , reward, turn, inter):
    while node != None:
        node.visits += 1
        node.reward -= turn*reward
        node = node.parent
        turn *= -1
        if (mode != "play"):
            tree_d = {}
            transformation(root_node, tree_d)
            n = NodeGUI("backup", tree_d, inter)
            tree_frames.append(n)
    return

## GUI Configuration
class Info(Frame):
    ## Message in the top of screen
    def __init__(self, master=None):
        Frame.__init__(self)
        self.configure(width=500, height=100, bg="white")
        police = tkFont.Font(family="Arial",size=36,weight="bold") 
        self.t = Label(self, text="Connect 4 AI exploration", font=police, bg ="white")
        self.t.grid(sticky=NSEW, pady=20)

class Point(object):
    ## Each one of the circles in the board
    def __init__(self, x, y, canvas, color="white"):
        self.canvas = canvas
        self.x = x
        self.y = y
        self.color = color
        self.turn = 1
        self.r = 30
        self.point = self.canvas.create_oval(self.x+10,self.y+10,self.x+61,self.y+61,fill=color,outline="blue")

    def setColor(self, color):
        self.canvas.itemconfigure(self.point, fill=color)
        self.color = color
class Text(object):
    def __init__(self, x, y, canvas, text):
        self.canvas = canvas
        self.x = x
        self.y = y
        self.text = text
        self.text_canvas = self.canvas.create_text(self.x+35, self.y+35, text=text)

    def setText(self, text):
        self.canvas.itemconfigure(self.text_canvas, text=text)
        self.text = text
def transformation(curr, tree_list):
    #node_str = str(curr.state) + '\nR:' + str(curr.reward) + '\nV:' +str(curr.visits)
    children_list = []
    
    if len(curr.children) != 0:
        for child in curr.children:
           children_list.append(str(child))
    tree_list[str(curr)] = children_list
    if len(curr.children) != 0:
        for child in curr.children:
            transformation(child, tree_list)
    return
        
def traversal(mini_node, edges):
    if len(mini_node.next) != 0:
        for sub in mini_node.next:
            edges.append((str(mini_node), str(sub)))
            traversal(sub, edges)


#player-- 0 human, 1 MTCS, 2 Random, 3 MiniMax 4. Expectimax
class Terrain(Canvas):
    ## Board visual representation
    def __init__(self, master=None):

        Canvas.__init__(self)
        self.configure(width=500, height=400, bg="green")

        self.p = []
        self.winner = False
        #self.player1 = player1
        #self.player2 = player2
        board = [] 
        for i in range(6):
            row = []
            for j in range(7):
                row.append(0)
            board.append(row)

        self.b = Board( board )
        self.last_bstate = self.b
        
        for i in range(0, 340, int(400/6)):
            spots = []
            for j in range(0, 440, int(500/7)):
                spots.append(Point(j, i ,self))
                
            self.p.append(spots)
        self.txt = []
        for j in range(0, 440, int(500/7)):
            self.txt.append(Text(j, i, self, "0"))
        self.bind("<Button-1>", self.action)

    def reloadBoard(self, i=None, j=None, val=None, bstate=None):
        """
        Reloads the board colors and content.
        Uses recursive upload for more complex cases (e.g. step back).
        [i,j,val] or [bstate] can be provided (but not simpultaneously).
        If no i, j, values or bstate are provided, it updates only colors.
        I bstate is present, updates the board values first and then colors.
        If i and j is present but no val, then updates the color of only one cell.
        If i and j and val are present, updates the matrix and the color.
        """
        if i==None:
            if bstate!=None:
                self.b = copy.deepcopy(bstate)
            for i in range(6):
                for j in range(7):
                    self.reloadBoard(i, j, val=None, bstate=None)
        elif val==None:
            if self.b.board[i][j] == -1:
                self.p[i][j].setColor("yellow")
            elif self.b.board[i][j] == 1:
                self.p[i][j].setColor("red")
            elif self.b.board[i][j] == 0:
                self.p[i][j].setColor("white")
        else:
            self.b.board[i][j] = val
            self.reloadBoard(i, j)
    
    def reloadText(self):
        for i in range(7):
            self.txt[i].setText(show_utilites[i])

    def findBestMove(self , factor, algorithm ):
    # Returns the best move using MonteCarlo Tree Search
        #global tree_dic
        # algorithm: Random/MiniMax/Alpha Beta/...
        global tree_frames

        tree_frames = []
        if algorithm == "MiniMax":
            bestMove = MiniMax(self.b)
            self.b = bestMove #Board
        elif algorithm == "alphabeta":
            bestMove = alpha_beta_search(self.b)
            self.b = bestMove #Board
        elif algorithm == "Monto":
            o = Node(self.b)
            bestMove = MTCS(iteration_count,o,factor)
            self.b = copy.deepcopy(bestMove.state)
        elif algorithm == "Random":
            self.b = self.b.move(random_player(self.b), 1)

        

        self.reloadBoard()
        self.reloadText()


    def action(self, event):

        self.last_bstate = copy.deepcopy(self.b)

        # Human Action
        if not self.winner:
            col = int(event.x/71)
            ok = False 
            row = self.b.tryMove( col )

            if row == -1:
                return 
            else:
                self.reloadBoard(row, col, -1)
                self.b.last_move = [row, col]
                ok = True

            if ok:
                info.t.config(text="Computer's Turn")

            result = self.b.winner()

            #Check if there is a winner or if it ended in a draw
            if result == 1:
                info.t.config(text="You lost!")
                self.winner = True 
            elif result == -1:
                info.t.config(text="You won!")
                self.winner = True
            elif self.b.terminal():
                info.t.config(text="Draw")
                self.winner = True

        self.update()

        # Computer Action     
        if not self.winner:

            self.findBestMove(factor_input, algorithm)
            ok = True

            if ok:
                info.t.config(text="Your turn")

            result = self.b.winner()

            if result == 1 :
                info.t.config(text="You lost!")
                self.winner = True
            elif result == -1:
                info.t.config(text="You won!")
                self.winner = True
            elif self.b.terminal():
                info.t.config(text="Draw")
                self.winner = True

        self.update()
   

if __name__ == "__main__":

    evaluation_temp = "Simple evaluation"
    mode = 'tutorial'
    root = Tk()
    root.geometry("920x800")
    root.title("Connect 4 game tree Visualization")
    root.configure(bg="white")

    #root.minsize(800,700)
    #root.maxsize(800,700)
    tree_frames = []

    algorithm = "Random"#"alphabeta"#"MiniMax" #Monto
    show_utilites = [0, 0, 0, 0, 0, 0, 0]
    
    iteration_count = 300
    
    
    def restart_play():
        global info
        global mode
        global iteration_count
        global depth
        global evaluation
        global evaluation_temp
        global mode_s
        mode_s.set("Mode: Play")
        info.t.config(text="")
        mode = 'play'
        iteration_count = play_iteration
        depth = m_scale_widget.get()
        evaluation = evaluation_temp
        info = Info(root)
        info.grid(row=0, column=0, columnspan=3)
        t = Terrain(root)
        t.grid(row=1, column=0, rowspan=5, columnspan=3)
    def restart_tutorial():
        global info
        global mode
        global iteration_count
        global depth
        global evaluation
        global evaluation_temp
        global mode_s
        mode_s.set("Mode: Tutorial")

        info.t.config(text="")
        mode = 'tutorial'
        iteration_count = t_scale_widget.get()
        depth = m_t_scale_widget.get()
        evaluation = evaluation_temp
        info = Info(root)
        info.grid(row=0, column=0, columnspan=3)

        t = Terrain(root)
        t.grid(row=1, column=0, rowspan=5, columnspan=3)

    def select_algo(select_algo):
        global title_s
        global random_frame
        global monto_carlo
        global minimax_frame
        global mode
        global algorithm
        if select_algo == "MonteCarlo":

            monto_carlo.tkraise()
            title_s.set("Monte Carlo AI Parameters \n" )
            algorithm = "Monto"
        elif select_algo == "Random":
            random_frame.tkraise()
            title_s.set("Random Move")
            algorithm = "Random"
        elif select_algo == "MiniMax":
            minimax_frame.tkraise()
            title_s.set("MiniMax AI Parameters \n" )
            algorithm = "MiniMax"
        elif select_algo == "AlphaBeta":
            minimax_frame.tkraise()
            title_s.set("AlphaBeta AI Parameters \n" )
            algorithm = "alphabeta"
        restart_tutorial()


    def step_back():
        global t
        t.step_back()

    def close():
        root.destroy()
    
    def get_eval(*args):
        global evaluation_temp
        global m_variable
        evaluation_temp = m_variable.get()

    
    def test_animation():
        if (mode == 'play'):
            messagebox.showinfo("Alert", "Currently play mode, no Visualization, pls switch to tutorial mode")
            return
        if (algorithm == 'Random'):
            messagebox.showinfo("Alert", "Random AI doesn't have Visualization")
            return
        p = 0
        global tree_frames
        fig = plt.figure(figsize=(20,6.5))
        pause = False      
        def anim(t):
            nonlocal p
            plt.clf()
            plt.cla()
            #g.clear()

            g = nx.DiGraph(tree_frames[p].tree_dic)
            color = 'none'
            color_map = []
            color_map += g.number_of_nodes() * [color]

            if (len(tree_frames[p].add_edges) != 0):
                extra_edges = tree_frames[p].add_edges
                g.add_edges_from(extra_edges)
                color_map += (g.number_of_nodes() - len(color_map)) * ['lightblue']
            plt.title("Game Tree Visualization: " + tree_frames[p].stage + " iteration: " + str(tree_frames[p].iteration))
            p  = p + 1
            pos = graphviz_layout(g, prog='dot')
            

            #nx.draw(g, pos, with_labels=True, arrows=True, font_weight='bold', width=3, node_size=1500, font_size=4)            
 
            nx.draw(g, pos, with_labels=True, arrows=True, font_weight='bold', width=1,node_color=color_map,node_shape='s',bbox=dict(facecolor='none', edgecolor='red'), node_size=1300, font_size=5)
        def anim_mini(t):
            nonlocal p
            global mini_edges
            plt.clf()
            plt.cla()
            #g.clear()

            g = nx.DiGraph()


            
            plt.title("Game Tree Visualization for " + algorithm)
            edges = []
            traversal(tree[mini_edges], edges)
            g.add_edges_from(edges)
            mini_edges += 1
            pos = graphviz_layout(g, prog='dot')
            

            #nx.draw(g, pos, with_labels=True, arrows=True, font_weight='bold', width=3, node_size=1500, font_size=4)            
 
            nx.draw(g, pos, with_labels=True, arrows=True, font_weight='bold', width=1,node_shape='s',bbox=dict(facecolor='none', edgecolor='red'), node_size=1300, font_size=5)
        
            
        def onClick(event):
            nonlocal pause
            if event.dblclick:
                if (pause):
                    ani.event_source.start()
                    pause = False
                else:
                    ani.event_source.stop()
                    pause = True

        if len(tree_frames) > 0 and algorithm == 'Monto':
            fig.canvas.mpl_connect('button_press_event', onClick)
            ani = FuncAnimation(fig, anim, repeat=False, frames=len(tree_frames) - 1, interval=20)
            plt.show()
            #writervideo = FFMpegWriter(fps=1) 
            #ani.save('animation.mp4', writer=writervideo)
        elif len(tree) > 0:# and algorithm != "MiniMax":
            global mini_edges

            mini_edges = 0
            fig.canvas.mpl_connect('button_press_event', onClick)
            ani = FuncAnimation(fig, anim_mini, repeat=False, frames=len(tree) - 1, interval=20)
            plt.show()

    
        


    info = Info(root)
    #info.t.config(text="")
    info.grid(row=0, column=0, columnspan=3)

    t = Terrain(root)
    t.grid(row=1, column=0, rowspan=5, columnspan=3)
    

    ins_v = StringVar(root)
    insv_label = Label(root,  textvariable=ins_v, bg='white')
    ins_v.set("Instuctions:\
        \nTwo Mode: \
        \n play mode - higher iteration/deeper depth('smarter' AI)\
        \n tutorial mode - game tree animation\
        \n\
        \nUser guide for animation:\
        \n 1. double click to pause/play \
        \n 2. use zoom button \
        \nto zoom in some overlapping nodes\
        \n R is reward, V is visit times\
        \n\
        \nMonte Carlo Game Tree:\
        \nExpansion: add possibel states to child node\
        \nSelection: choose best score UCT\
        \nSimulation: choose next move until win/lost/draw\
        \nBackpropagation: update visits and reward from new node to root\
        \n Only tutorial mode has Visualization function\
        \n\
        \nMiniMax or Alpha Beta Game Tree:\
        \nUtility is caculated at leaves or depth==0\
        \nassume that human always select best one(min one),\
        \nAI move always select max\
        \nTwo Evaluation ways: simple and advanced evaluation function\
        \nFor more details: Please go to the website attached")
    insv_label.grid(row=0, column=3,columnspan=2, rowspan=5, sticky=E+W)
    
    title_s = StringVar()
    algo_title = Label(root,  textvariable=title_s, font=("Arial", 25), bg='white' )
    title_s.set("Random Move")
    algo_title.grid(row=5, column=3, columnspan=2,sticky=E+W)

    #Monto Carlo frame
    monto_carlo = Frame(root)
    monto_carlo.grid(row=6, column=3, sticky="nsew", rowspan=3, columnspan=2)
    

    fac_l = StringVar()
    fac_label = Label(monto_carlo,  textvariable=fac_l)
    fac_l.set("UTC Factor: ")
    fac_label.grid(row=0, column=0,columnspan=2, sticky=E+W)

    fac_s = Scale(monto_carlo, from_=0, to=30, orient=HORIZONTAL)
    fac_s.set(2)
    fac_s.grid(row=1, column=0,columnspan=2, sticky=E+W)
    factor_input = fac_s.get()

    ite = StringVar()
    ite_label = Label(monto_carlo,  textvariable=ite)
    ite.set("Simulation Iteration(play mode):")
    ite_label.grid(row=2, column=0, sticky=E+W)
    
    scale_widget = Scale(monto_carlo, from_=1, to=1000, orient=HORIZONTAL)
    scale_widget.set(300)
    scale_widget.grid(row=3, column=0, sticky=E+W)
    play_iteration = scale_widget.get()

    t_ite = StringVar()
    t_ite_label = Label(monto_carlo,  textvariable=t_ite)
    t_ite.set("Simulation Iteration(tutorial mode):")
    t_ite_label.grid(row=2, column=1, sticky=E+W)

    t_scale_widget = Scale(monto_carlo, from_=1, to=30, orient=HORIZONTAL)
    t_scale_widget.set(15)
    t_scale_widget.grid(row=3, column=1, sticky=E+W)
    tutorial_iteration = t_scale_widget.get()


    #MiniMax frame
    minimax_frame = Frame(root)
    minimax_frame.grid(row=6, column=3, sticky="nsew", rowspan=3, columnspan=2)
    
    m_it = StringVar()
    m_it_label = Label(minimax_frame,  textvariable=m_it)
    m_it.set("Evaluation function selection:")
    m_it_label.grid(row=0, column=0, columnspan=2, sticky=E+W)

    m_variable = StringVar(value='Simple evaluation')
    evaluation_box = OptionMenu(minimax_frame,m_variable, 'Simple evaluation', 'Advanced evaluation')
    evaluation_box.grid(row=1, column=0, columnspan=2, sticky=E+W)
    m_variable.trace("w", get_eval)

    it = StringVar()
    it_label = Label(minimax_frame,  textvariable=it)
    it.set("Depth(play mode, more faster):")
    it_label.grid(row=2, column=0, sticky=E+W)
    
    m_scale_widget = Scale(minimax_frame, from_=1, to=10, orient=HORIZONTAL)
    m_scale_widget.set(2)
    m_scale_widget.grid(row=3, column=0, sticky=E+W)
    d_depth = m_scale_widget.get()

    m_t_ite = StringVar()
    m_t_ite_label = Label(minimax_frame,  textvariable=m_t_ite)
    m_t_ite.set("Depth(tutorial mode with vis):")
    m_t_ite_label.grid(row=2, column=1, sticky=E+W)

    m_t_scale_widget = Scale(minimax_frame, from_=1, to=3, orient=HORIZONTAL)
    m_t_scale_widget.set(3)
    m_t_scale_widget.grid(row=3, column=1, sticky=E+W)
    l_depth = m_t_scale_widget.get()
    #monto_carlo.tkraise()

    #Random
    random_frame = Frame(root)
    random_frame.grid(row=6, column=3, sticky="nsew", rowspan=3, columnspan=2)

    #messagebox.showinfo("Title", "a Tk MessageBox")
    Button(root, text="Start play mode", command=restart_play, fg='blue').grid(row=10, column=3, sticky=E+W)
    Button(root, text="Start tutorial mode", command=restart_tutorial, fg='blue').grid(row=10, column=4, sticky=E+W)

    opponent_title = Label(root,  font=("Arial", 20), bg="white",text="Choose Your Opponent below")
    opponent_title.grid(row=6, column=1,columnspan=2, sticky=E+W)
    Button(root, text="MiniMax AI", command=lambda: select_algo("MiniMax")).grid(row=7, column=1,columnspan=2, sticky=E+W)
    Button(root, text="Random Move", command=lambda: select_algo("Random")).grid(row=8, column=1,columnspan=2, sticky=E+W)
    Button(root, text="Monte Carlo AI", command=lambda: select_algo("MonteCarlo")).grid(row=9, column=1,columnspan=2, sticky=E+W)
    Button(root, text="Alpha-beta AI", command=lambda: select_algo("AlphaBeta")).grid(row=10, column=1,columnspan=2, sticky=E+W)

    mode_s = StringVar()
    mode_label = Label(root,  textvariable=mode_s, font=("Arial", 25), bg='white' )
    mode_s.set("Mode: Tutorial")
    mode_label.grid(row=6, column=0, sticky=E+W)

    Button(root, text = "Exit", command = close).grid(row=7,column =0, sticky=E+W)
    Button(root, text="Game Tree Visualization", command=test_animation).grid(row=11, column=3,columnspan=2, sticky=E+W)

    root.mainloop()


