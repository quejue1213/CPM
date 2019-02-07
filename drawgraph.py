import networkx as nx
import matplotlib.pyplot as plt

G=nx.read_edgelist("test.txt")
pos=nx.spring_layout(G)
nx.draw(G,with_labels=True)
plt.show()
