###########################################################################################################
### Computer Aided Verification Project 
### Submitted by: Nagarajan Shanmuganathan
### email id: nash2533@colorado.edu

### This project is an implementation of the paper "An Algorithm for Strongly Connected Component
### Analysis in n log n Symbolic Steps" by Bloem, Gabow and Somenzi to decompose a graph into its SCCs. 
### This in turn is being used to decide the emptiness of a Street Automaton and Buchi Automaton. 


### Two input files: The file with the edge relationship which can be turned into a directed graph and 
### the other file with initial states of the automaton and the acceptance condition for the Street
### Automaton in the next following lines

### The program uses networkx library to work on most of the graph related operations; especially the 
### "ancestors" and "descendants" methods which are basically the preimage and image of a vertex in the
### graph, respectively. 

### The two main methods of the program are lockStep and report which are adapted directly from the paper.
### Detailed explanation on how those procedures work is given in the paper. 

### To run the program: python3 scc_decomposition.py graph.adjlist conditions.txt

### Output: A graph plot which will highlight SCCs with same color for both nodes and (thick) edges in the
### SCCs. The console output will have the outputs for the SCCs for which the language is not empty.
###########################################################################################################

import networkx as nx
import matplotlib.pyplot as plt
import matplotlib as mpl
import random
import sys

def createAdjDict(lines):
	adj_dict = dict()
	for line in lines:
		line_split = line.split(" ")
		remaining = line_split[1:]
		remaining[len(remaining) - 1] = remaining[len(remaining) - 1].rstrip('\n')
		adj_dict.update({ line_split[0] : remaining })

	return adj_dict

def createAllEdges(adj_dict):
	edge_list = set()
	for (key, value) in adj_dict.items():
		for adj_vertex in value:
			edge_list = edge_list | { (key, adj_vertex) }

	return edge_list

def plotGraph(G, sccs, adj_dict):
	colors = { 'red', 'blue', 'green', 'black', 'grey', 'yellow', 'orange' }
	pos = nx.layout.circular_layout(G)
	scc_nodes = []
	
	all_edges = createAllEdges(adj_dict)

	for scc in sccs:
		for scc_node in scc:
			scc_nodes.append(scc_node)

	trivial_sccs = []
	for graph_node in G:
		if graph_node not in scc_nodes:
			trivial_sccs.append(graph_node)
	
	for scc in sccs:
		scc_list = list(scc)
		if len(colors) != 0:
			color = colors.pop()
		else:
			color = 'cyan'

		nx.draw_networkx_nodes(G, pos, nodelist=scc_list, node_color=color, node_size=300)

		edge_list = list()
		for node in scc_list:
			adj_vertices = adj_dict[node]
			
			for vertex in adj_vertices:
				if vertex in scc_nodes and vertex in scc_list:
					edge_list.append( (node, vertex) )
					all_edges.remove( (node, vertex) )

		nx.draw_networkx_edges(G, pos, edgelist=edge_list, 
			arrowstyle='->', arrowsize=10, 
			edge_cmap=plt.cm.Blues, width=2, edge_color=color)
		
	all_edges = list(all_edges)

	if len(colors) != 0:
		color = colors.pop()
	else: 
		color = 'orange'

	nx.draw_networkx_nodes(G, pos, nodelist=trivial_sccs, node_color=color, node_size=300)
	
	edges = nx.draw_networkx_edges(G, pos, edgelist=all_edges, arrowstyle='->',
	                               arrowsize=10,
	                               edge_cmap=plt.cm.Blues, width=1, edge_color='violet')
	labels = nx.draw_networkx_labels(G, pos, font_size=8, font_color='white', font_weight='bold')
	
	plt.show()

def getImage(G, Ffront):
	img_union = set()
	for node in Ffront:
		img = nx.descendants(G, node)
		img_union = img_union | img
		
	return img_union

def getPreimage(G, Bfront):
	preimg_union = set()
	for node in Bfront:
		preimg = nx.ancestors(G, node)
		preimg_union = preimg_union | preimg

	return preimg_union

def lockStep(G, nodes, initial_nodes, acceptance_condition, sccs):
	if len(nodes) == 0:
		return 

	# Random sample of a vertex from the current set of nodes
	v = random.sample(nodes, 1)[0]
	print(len(nodes))

	F = { v }
	Ffront = { v }
	B = { v }
	Bfront = { v }

	while len(Ffront) != 0 and len(Bfront) != 0:
		img = getImage(G, Ffront)
		img_intersection = img & nodes
		Ffront = img_intersection - F

		preimg = getPreimage(G, Bfront)
		preimg_intersection = preimg & nodes
		Bfront = preimg_intersection - B

		F = F | Ffront
		B = B | Bfront

	converged = set()
	if len(Ffront) == 0:
		converged = F
	else:
		converged = B

	while len(Ffront & B) != 0 or len(Bfront & F) != 0:
		img = getImage(Ffront)
		img_intersection = img & nodes
		Ffront = img_intersection - F

		preimg = getPreimage(G, Bfront)
		preimg_intersection = preimg & nodes
		Bfront = preimg_intersection - B

		F = F | Ffront
		B = B | Bfront

	C = F & B

	report(G, nodes, initial_nodes, acceptance_condition, C, sccs)

	lockStep(G, converged - C, initial_nodes, acceptance_condition, sccs)
	lockStep(G, nodes - converged, initial_nodes, acceptance_condition, sccs)


def report(G, nodes, initial_nodes, acceptance_condition, C, sccs):
	c_prime = set()

	print('SCC: ', C)

	if len(C) == 1 or len(C) == 0:
		return

	fair = True
	for condition in acceptance_condition:
		if len(C & { condition[0] }) != 0:
			if len(C & { condition[1] }) == 0:
				fair = False
				break

	if fair:
		print("SCC is fair; language is not empty")
		sccs.append(C)
		return 

	c_prime = C

	for condition in acceptance_condition:
		if len(C & { condition[0] }) != 0 and len(C & { condition[1] }) == 0:
			c_prime = c_prime - condition[0]

	if len(c_prime) != 0:
		lockStep(G, c_prime, initial_nodes, acceptance_condition, sccs)

if __name__ == '__main__':

	if(len(sys.argv) is not 3):
		print("Please load the input files")
		sys.exit()

	args = sys.argv

	graph_file = open(args[1], 'r')
	lines = graph_file.readlines()
	G = nx.parse_adjlist(lines, create_using=nx.DiGraph)

	print("Num edges: ", G.number_of_edges())
	print("Num nodes: ", G.number_of_nodes())

	nodes = set(G.nodes)
	edges = set(G.edges)

	adj_dict = createAdjDict(lines)

	conditions = open(args[2], 'r')

	lines = conditions.readlines()

	initial_nodes = set()
	line_nodes = lines[0].split(" ")

	for node in line_nodes:
		initial_nodes = initial_nodes | { int(node.rstrip('\n')) }

	print("Initial states: ", initial_nodes)

	acceptance_condition = list()
	for i in range(1, len(lines)):
		line_nodes = lines[i].split(" ")
		lu_condition = (int(line_nodes[0]), int(line_nodes[1].rstrip('\n')))
		acceptance_condition.append(lu_condition)

	print("Acceptance conditions: ", acceptance_condition)

	sccs = list()

	lockStep(G, nodes, initial_nodes, acceptance_condition, sccs)

	print("Non-trivial SCCs: ", sccs)

	plotGraph(G, sccs, adj_dict)
