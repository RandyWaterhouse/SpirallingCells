"""
   SpirallingCells: A Cellular Automaton

   by Dr. Peter U.

   Version 1.0, March 2017

   See: https://github.com/RandyWaterhouse/SpirallingCells

"""

######################################################################
#
# import packages:
import sys
import time
import math
import random
import pygame
from pygame.locals import *
from copy import deepcopy
import pickle
import datetime
import timeit
import cProfile
from Tkinter import *
import Tkinter, Tkconstants, tkFileDialog


######################################################################
#
# global constants:
MAIN_WIDTH = 800      # width of cellular automaton output
MENU_WIDTH = 200      # width of control section
HEIGHT = 800          # height of cellular automaton output
HEADER_HEIGHT = 45   # height of header 
VERBOSE = True        # if True, give chatty status outputs to stdout
FONTSIZE = 20         # font size for control section buttons
COLORS = {"WHITE": (255, 255, 255), "RED": (255, 0, 0), "GREEN": (0, 255, 0),
          "BLUE": (0, 0, 255), "BLACK": (0, 0, 0), "YELLOW": (255, 255, 0),
          "LIGHT_BLUE": (0, 125, 227), "GREY1": (120, 120, 120),
          "GREY2": (224, 224, 224), "LIGHTBLUE": (102, 178, 255),
          "LIGHTRED": (255, 153, 153), "LIGHTYELLOW": (255, 255, 153),
          "PINK": (255, 51, 255), "DARKBLUE": (0, 0, 153),
          "LAVENDER": (204, 153, 255), "LIGHTGREEN": (153, 255, 204),
          "BROWN": (102, 51, 0), "OLIVE": (153, 153, 0)}
COLOR_SEQ = ["BLUE", "YELLOW", "BROWN", "RED", "GREY2", "GREEN", "WHITE",
             "DARKBLUE", "PINK", "OLIVE", "LIGHTBLUE", "LIGHTRED",
             "LIGHTGREEN", "BLACK", "GREY1", "LAVENDER"]
PALETTE = [COLORS[color] for color in COLOR_SEQ]
VERSION = "1.0"       # program version

######################################################################
#
# global variables:
neighbourhood = "von Neumann"    # cell neighbourhood: von Neumann or Moore
num_states = 8                   # number of possible states for cellular automaton
iteration = 0                    # counter for interation number
cell_size = 2                    # cell size for drawing (as square with sidelength cell_size)
running = True                   # keep track of whether simulation is paused or not
show_mindist = False             # show entropy, this slows simulation 

######################################################################
#
# helper functions:
#
# draw text on PyGame surface:
def draw_text(surface, font, text, position, color):
        lable = font.render(text, 1, color)
        surface.blit(lable, position)

# construct filename from current date and time:
def get_filename(prefix, num_states, cell_size, width, height, postfix):
    now = datetime.datetime.now()
    filename = prefix + now.strftime("%Y%m%d_%H%M") + "_" + str(num_states) + \
               "_" + str(cell_size) + "_" + str(width) + "_" + str(height) + "." + \
               postfix
    return filename


######################################################################
#
# Button class for control section, PyGame doesn't have ready-to-use
# buttons or similar:
class Button():

    def __init__(self, width, height, text, color, tcolor):
        self.width = width
        self.height = height
        self.text = text
        self.color = color
        self.tcolor = tcolor

    def SetText(self, text):
        self.text = text

    def PlaceButton(self, surface, x, y):
        self.x = x
        self.y = y
        surface = self.DrawButton(surface, x, y)
        surface = self.ButtonText(surface, x, y)

    def DrawButton(self, surface, x, y):
        pygame.draw.rect(surface, self.color, (x, y, self.width, self.height), 0)
        return surface

    def ButtonText(self, surface, x, y):
        font_size = int(self.width // len(self.text))
        font = pygame.font.SysFont("Arial", FONTSIZE)
        text = font.render(self.text, 1, self.tcolor)
        surface.blit(text, ((x + self.width/2) - text.get_width()/2, (y + self.height/2) - text.get_height()/2))
        return surface

    def IsPressed(self, mouse):
        return mouse[0] > self.x and \
               mouse[1] > self.y and \
               mouse[0] <= self.x + self.width and \
               mouse[1] < self.y + self.height


######################################################################
#
# Cellular Automaton class, stores and evolves states:
class CellularAutomaton():

    def __init__(self, w, h, num_states, cell_size, random_start=True):
        # initialize cellular automaton with width w, height h and
        # num_states number of states:
        self.width = w
        self.height = h
        self.num_states = num_states
        self.cell_size = cell_size
        self.grid = [[0 for col in range(w)] for row in range(h)]
        if random_start:
            self.InitializeRandomly()
        self.iterations = 0
        self.num_cells = w * h
        self.offsets = {"Moore": [[0, 1], [0, -1], [1, 0], [-1, 0],
                                 [1, 1], [1, -1], [-1, 1], [-1, -1]],
                        "von Neumann": [[0, 1], [0, -1], [1, 0], [-1, 0]]}

    def InitializeRandomly(self, seed=None):
        # initialize CA with random values:
        if seed != None:
            random.seed(seed)
        self.grid = [[random.randint(0, self.num_states - 1) \
                      for col in range(self.width)] \
                     for row in range(self.height)]
        self.initial_grid = deepcopy(self.grid)

    def ResetGrid(self):
        # reset CA to last initial values so simulation can be restarted:
        self.iterations = 0
        self.grid = deepcopy(self.initial_grid)

    def GetGrid(self):
        # return CA data (grid):
        return self.grid[:]

    def HasPlusOneNeighbour(self, row, col, neighbourhood):
        # check whether cell at position (row, col) has at least one
        # neighbour in a state one higher (mod N) than the cell in question:
        target = (self.grid[row][col] + 1) % self.num_states
        for row_off, col_off in self.offsets[neighbourhood]:
            row2 = (row + row_off) % self.height
            col2 = (col + col_off) % self.width
            if self.grid[row2][col2] == target:
                return True
        return False
        
    def NeighbourValues(self, row, col, neighbourhood):
        # unused at this time
        target = (self.grid[row][col] + 1) % self.num_states
        for row_off, col_off in self.offsets[neighbourhood]:
            row2 = (row + row_off) % self.height
            col2 = (col + col_off) % self.width
            if self.grid[row2][col2] == target:
                return True
        return False

    def EvolveOneStep(self, neighbourhood):
        # evolve CA one generation:
        self.grid = [[self.grid[row][col] if not self.HasPlusOneNeighbour(row, col, neighbourhood) \
                     else (self.grid[row][col] + 1) % self.num_states \
                     for col in range(self.width)] for row in range(self.height)]
        self.iterations += 1
        return self.iterations
        
    def DrawCells(self, surface):
        # draw CA on screen:
        for row in range(self.height):
            for col in range(self.width):
                color = PALETTE[self.grid[row][col]]
                surface.fill(color, (col*self.cell_size, HEADER_HEIGHT + row*self.cell_size, self.cell_size, self.cell_size), 0)
        return surface

    def SaveImage(self, surface):
        # save current graphics output as PNG image file:
        filename = get_filename("SpirallingCells_image_", self.num_states, self.cell_size, self.width, self.height, "png")
        pygame.image.save(surface, filename)
        return filename
    
    def GetMinDiff(self, row, col, neighbourhood):
        # calculate minimum difference in states between cell at position
        # (row, col) and it's neighbours
        min_diff = 10 * self.num_states
        offsets = {"Moore": [[0, 1], [0, -1], [1, 0], [-1, 0],
                             [1, 1], [1, -1], [-1, 1], [-1, -1]],
                   "von Neumann": [[0, 1], [0, -1], [1, 0], [-1, 0]]}
        this_state = self.grid[row][col]
        for row_off, col_off in offsets[neighbourhood]:
            row2 = (row + row_off) % self.height
            col2 = (col + col_off) % self.width
            other_state = self.grid[row2][col2]
            min_diff = min(min_diff, abs((this_state - other_state) % self.num_states), \
                           abs((other_state - this_state) % self.num_states))
        return min_diff

    def GetEntropy(self, neighbourhood):
        # calculate average MinDist value over all cells:
        ent = 0
        for row in range(self.height):
            for col in range(self.width):
                ent += self.GetMinDiff(row, col, neighbourhood)
        return float(ent) / self.num_cells

    def SaveInitial(self, neighbourhood):
        # save initial configuration to pickle file:
        filename = get_filename("SpirallingCells_initial_", self.num_states, \
                                self.cell_size, self.width, self.height, "p")
        f = open(filename, "wb")
        pickle.dump(self.num_states, f)
        pickle.dump(self.width, f)
        pickle.dump(self.height, f)
        pickle.dump(self.cell_size, f)
        pickle.dump(neighbourhood, f)
        pickle.dump(self.initial_grid, f)
        pickle.dump(0, f)
        f.close()
        return filename

    def SaveCurrent(self, neighbourhood):
        # save current configuration to pickle file:
        filename = get_filename("SpirallingCells_current_", self.num_states, \
                                self.cell_size, self.width, self.height, "p")
        f = open(filename, "wb")
        pickle.dump(self.num_states, f)
        pickle.dump(self.width, f)
        pickle.dump(self.height, f)
        pickle.dump(self.cell_size, f)
        pickle.dump(neighbourhood, f)
        pickle.dump(self.grid, f)
        pickle.dump(self.iterations, f)
        f.close()
        return filename

    def LoadState(self):
        # load configuration from pickle file, filename is chosen via
        # an "askopenfilename" dialog in tkinter:
        tk_root = Tk()
        file_path = tkFileDialog.askopenfilename()
        f = open(file_path, "rb")
        self.num_states = pickle.load(f)
        self.width = pickle.load(f)
        self.height = pickle.load(f)
        self.cell_size = pickle.load(f)
        neighbourhood = pickle.load(f)
        self.grid = pickle.load(f)
        self.iterations = pickle.load(f)
        f.close()
        tk_root.destroy()
        return neighbourhood


        
######################################################################
#
# PyGame main loop:
def main_loop(surface):
    global neighbourhood, num_states, iteration, cell_size, running, show_mindist

    # create cellular automaton instance:
    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
    
    # build control section:
    button_start = Button(70, 30, "Start", COLORS["GREEN"], COLORS["BLACK"])
    button_pause = Button(70, 30, "Pause", COLORS["LIGHTRED"], COLORS["BLACK"])
    button_continue = Button(70, 30, "Continue", COLORS["GREEN"], COLORS["BLACK"])
    button_restart = Button(70, 30, "Restart", COLORS["GREEN"], COLORS["BLACK"])
    button_quit = Button(70, 30, "Quit", COLORS["RED"], COLORS["BLACK"])
    button_neighbourhood_neumann = Button(90, 30, "Neumann", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_neighbourhood_moore = Button(90, 30, "Moore", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_ncell_4 = Button(70, 30, "4", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_ncell_8 = Button(70, 30, "8", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_ncell_12 = Button(70, 30, "12", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_ncell_16 = Button(70, 30, "16", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_save_current = Button(70, 30, "current", COLORS["LIGHTYELLOW"], COLORS["BLACK"])
    button_save_initial = Button(70, 30, "initial", COLORS["LIGHTYELLOW"], COLORS["BLACK"])
    button_save_image = Button(70, 30, "image", COLORS["LIGHTYELLOW"], COLORS["BLACK"])
    button_load_current = Button(70, 30, "load", COLORS["LIGHTYELLOW"], COLORS["BLACK"])
    button_cell_size1 = Button(70, 30, "1", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_cell_size2 = Button(70, 30, "2", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_cell_size3 = Button(70, 30, "3", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_cell_size4 = Button(70, 30, "4", COLORS["LIGHTBLUE"], COLORS["BLACK"])
    button_toggle_entropy = Button(120, 30, "switch off", COLORS["LIGHTBLUE"], COLORS["BLACK"])

    last_grid = CA.GetGrid()
    
    while True:
        # loop until user event triggers some action:

        # draw window and title:
        surface.fill(COLORS["GREY2"])
        surface.fill(COLORS["LIGHTYELLOW"], (0, 0, MAIN_WIDTH + MENU_WIDTH, HEADER_HEIGHT), 0)
        draw_text(surface, helv24, "SpirallingCells " + VERSION + \
                  " ==> https://github.com/RandyWaterhouse/SpirallingCells", (10, 10), COLORS["BLUE"])
        draw_text(surface, helv24, "by Dr. Peter U.", (MAIN_WIDTH + 25, 10), COLORS["BLUE"])

        # place buttons in control section on right-hand side:
        button_start.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 30)
        button_pause.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 30)
        button_continue.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 70)
        button_restart.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 70)
        button_quit.PlaceButton(surface, MAIN_WIDTH + 55, HEADER_HEIGHT + 110)
        button_neighbourhood_neumann.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 230)
        button_neighbourhood_moore.PlaceButton(surface, MAIN_WIDTH + 105, HEADER_HEIGHT + 230)
        button_ncell_4.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 320)
        button_ncell_8.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 320)
        button_ncell_12.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 360)
        button_ncell_16.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 360)
        button_save_current.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 440)
        button_save_initial.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 440)
        button_save_image.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 480)
        button_load_current.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 480)
        button_cell_size1.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 560)
        button_cell_size2.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 560)
        button_cell_size3.PlaceButton(surface, MAIN_WIDTH + 10, HEADER_HEIGHT + 600)
        button_cell_size4.PlaceButton(surface, MAIN_WIDTH + 100, HEADER_HEIGHT + 600)
        button_toggle_entropy.PlaceButton(surface, MAIN_WIDTH + 40, HEADER_HEIGHT + 720)
        
        # draw text and lines:
        draw_text(surface, helv24, "Controls:", (MAIN_WIDTH + 45, HEADER_HEIGHT + 0), COLORS["BLACK"])
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 0), (MAIN_WIDTH, HEIGHT), 2)
        #pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 0), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 0), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 150), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 150), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 270), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 270), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 400), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 400), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 520), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 520), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 640), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 640), 2)
        pygame.draw.line(surface, COLORS["GREY1"], (MAIN_WIDTH, HEADER_HEIGHT + 680), (MAIN_WIDTH+MENU_WIDTH, HEADER_HEIGHT + 680), 2)
        draw_text(surface, helv24, "Neighbourhood:", (MAIN_WIDTH + 15, HEADER_HEIGHT + 160), COLORS["BLACK"])
        draw_text(surface, helv24, neighbourhood, (MAIN_WIDTH + 20, HEADER_HEIGHT + 190), COLORS["BLUE"])
        draw_text(surface, helv24, "No of states:", (MAIN_WIDTH + 15, HEADER_HEIGHT + 280), COLORS["BLACK"])
        draw_text(surface, helv24, str(num_states), (MAIN_WIDTH + 160, HEADER_HEIGHT + 280), COLORS["BLUE"])
        draw_text(surface, helv24, "Save options:", (MAIN_WIDTH + 25, HEADER_HEIGHT + 410), COLORS["BLACK"])
        draw_text(surface, helv24, "Cell size:", (MAIN_WIDTH + 25, HEADER_HEIGHT + 530), COLORS["BLACK"])
        draw_text(surface, helv24, str(cell_size), (MAIN_WIDTH + 160, HEADER_HEIGHT + 530), COLORS["BLUE"])
        draw_text(surface, helv24, "Iteration:", (MAIN_WIDTH + 15, HEADER_HEIGHT + 650), COLORS["BLACK"])
        draw_text(surface, helv24, str(iteration), (MAIN_WIDTH + 120, HEADER_HEIGHT + 650), COLORS["BLUE"])
        draw_text(surface, helv24, "Min Dist:", (MAIN_WIDTH + 15, HEADER_HEIGHT + 690), COLORS["BLACK"])
        entropy_text = str(round(CA.GetEntropy(neighbourhood), 3)) if show_mindist else "---"
        draw_text(surface, helv24, entropy_text, (MAIN_WIDTH + 120, HEADER_HEIGHT + 690), COLORS["BLUE"])

        # evolve cellular automaton:
        if running:
            iteration = CA.EvolveOneStep(neighbourhood)
 
        # draw cells in main part of window:
        CA.DrawCells(surface)
        pygame.display.flip()

        # check for user events:
        for event in pygame.event.get():
            if event.type == QUIT:
                pygame.quit()
                return
            elif  event.type == KEYDOWN:
                if event.key in [K_ESCAPE, K_q]:
                    pygame.quit()
                    return
                elif event.key == K_SPACE:
                    if VERBOSE: print "Space pressed, toggle running."
                    running = not running
            elif event.type == MOUSEBUTTONDOWN:
                if button_start.IsPressed(pygame.mouse.get_pos()):
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                    running = True
                    if VERBOSE: print "Starting simulation."
                elif button_pause.IsPressed(pygame.mouse.get_pos()):
                    running = False
                    if VERBOSE: print "Pausing simulation."
                elif button_continue.IsPressed(pygame.mouse.get_pos()):
                    running = True
                    if VERBOSE: print "Continuing simulation."
                elif button_restart.IsPressed(pygame.mouse.get_pos()):
                    running = True
                    if VERBOSE: print "Restarting simulation."
                    CA.ResetGrid()
                    running = True
                elif button_neighbourhood_neumann.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Von Neumann Neighbourhood selected."
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                    neighbourhood = "von Neumann"
                elif button_neighbourhood_moore.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Moore Neighbourhood selected."
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                    neighbourhood = "Moore"
                elif button_ncell_4.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected number of states: 4"
                    num_states = 4
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_ncell_8.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected number of states: 8"
                    num_states = 8
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_ncell_12.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected number of states: 12"
                    num_states = 12
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_ncell_16.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected number of states: 16"
                    num_states = 16
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_save_current.IsPressed(pygame.mouse.get_pos()):
                    filename = CA.SaveCurrent(neighbourhood)
                    if VERBOSE: print "Current state saved, filename:", filename
                elif button_save_initial.IsPressed(pygame.mouse.get_pos()):
                    filename = CA.SaveInitial(neighbourhood)
                    if VERBOSE: print "Initial state saved, filename:", filename
                elif button_save_image.IsPressed(pygame.mouse.get_pos()):
                    filename = CA.SaveImage(surface)
                    if VERBOSE: print "Image saved, filename:", filename
                elif button_load_current.IsPressed(pygame.mouse.get_pos()):
                    neighbourhood = CA.LoadState()
                    if VERBOSE: print "Data loaded."
                elif button_cell_size1.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected cell size: 1"
                    cell_size = 1
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_cell_size2.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected cell size: 2"
                    cell_size = 2
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_cell_size3.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected cell size: 3"
                    cell_size = 3
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_cell_size4.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Selected cell size: 4"
                    cell_size = 4
                    CA = CellularAutomaton(MAIN_WIDTH // cell_size, HEIGHT // cell_size, num_states, cell_size)
                elif button_toggle_entropy.IsPressed(pygame.mouse.get_pos()):
                    show_mindist = not show_mindist
                    if show_mindist:
                        button_toggle_entropy.SetText("switch off")
                    else:
                        button_toggle_entropy.SetText("switch on")
                    if VERBOSE: print "Entropy on!" if show_mindist else "Entropy off!"
                elif button_quit.IsPressed(pygame.mouse.get_pos()):
                    if VERBOSE: print "Quit pressed!"
                    pygame.quit()
                    return
                
           
                    
######################################################################
#                         
# initialize PyGame:
if VERBOSE: print "Initializing...",
if HEIGHT + HEADER_HEIGHT < 800:
    print "Sorry, we need a total height of at least 800 pixels."
elif MAIN_WIDTH + MENU_WIDTH < 1000:
    "Sorry, we need a total width of at least 1000 pixels."
else:
    start_timer = timeit.default_timer()
    pygame.init()
    helv20 = pygame.font.SysFont("Helvetica", 20)
    helv24 = pygame.font.SysFont("Helvetica", 24)
    myfont24 = pygame.font.SysFont("monospace", 24)
    myfont32 = pygame.font.SysFont("monospace", 32)
    myfont64 = pygame.font.SysFont("monospace", 64)
    flags = DOUBLEBUF
    surface = pygame.display.set_mode((MAIN_WIDTH + MENU_WIDTH, HEIGHT + HEADER_HEIGHT), flags)
    surface.set_alpha(None)
    pygame.display.set_caption("SpirallingCells " + VERSION)
    if VERBOSE: print "Done."
    ######################################################################
    #
    # start PyGame main loop:
    if VERBOSE: print "Starting main loop."
    main_loop(surface)

    if VERBOSE: print "CPU Usage:", timeit.default_timer() - start_timer
