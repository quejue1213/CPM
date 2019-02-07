## Info:
Feel free to use these lines as you wish.  
- "cpm" stores (k-1)-cliques in memory and computes k-clique communities such as defined by Palla et al.
- "cpm1" and "cpm2" compute an approximation of the k-clique communities such as defined by Palla et al. It uses less memory.

## To compile:
"gcc cpm.c -O9 -o cpm".

## To execute:
"./cpm k edgelist.txt".
- k >= 3
- "edgelist.txt" should contain the graph: one edge on each line separated by a space (no self-loop or multiple edge please).
Will print the number of k-cliques and the number of k-clique communities.

## Contributors:

Maximilien Dansich  Marwan Ghanem and Sergey Kirgizov  
2017 - 2019  
http://bit.ly/danisch  
maximilien.danisch@gmail.com

