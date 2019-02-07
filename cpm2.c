/*
Info:
Feel free to use these lines as you wish.
This program computes an approximation of the k-clique communities such as defined by Palla et al.

To compile:
"gcc cpm.c -O9 -o cpm".

To execute:
"./cpm k edgelist.txt".
- k >= 3
- "edgelist.txt" should contain the graph: one edge on each line separated by a space (no self-loop or multiple edge please).
Will print the number of k-cliques and the number of k-clique communities.
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define NLINKS 100000000 //maximum number of edges, will automatically increase if needed
#define S1MAX 2//maximum size of sets of type 1, will automatically increase if needed
#define S2MAX 10000//maximum size of sets of type 2, will automatically increase if needed


typedef unsigned int Node;
typedef unsigned long int Edge;
typedef unsigned long long int Clique;
typedef unsigned char Kvalue;

//SPECIAL SPARSE GRAPH DATASTRUCTURE

typedef struct {
	Node s;
	Node t;
} edge;

typedef struct {
	Node node;
	Node deg;
} nodedeg ;

typedef struct {
	Node n;//number of nodes
	Edge e;//number of edges
	edge *edges;//list of edges

	Node *ns;//ns[l]: number of nodes in G_l
	Node **d;//d[l]: degrees of G_l
	Edge *cd;//cumulative degree: (starts with 0) length=n+1
	Node *adj;//truncated list of neighbors
	Node *rank;//ranking of the nodes according to degeneracy ordering
	//unsigned *map;//oldID newID correspondance
	Node max;

	Kvalue k;//value of k (l-clique)

	Kvalue *lab;//lab[i] label of node i
	Node **sub;//sub[l]: nodes in G_l

} specialsparse;

void freespecialsparse(specialsparse *g){
	Kvalue i,k=g->k;
	free(g->ns);
	for (i=2;i<k+1;i++){
		free(g->d[i]);
		free(g->sub[i]);
	}
	free(g->d);
	free(g->sub);
	free(g->cd);
	free(g->adj);
	free(g);
}

//Compute the maximum of three unsigned integers.
inline Node max3(Node a,Node b,Node c){
	a=(a>b) ? a : b;
	return (a>c) ? a : c;
}

specialsparse* readedgelist(char* edgelist){
	Edge e1=NLINKS;
	specialsparse *g=malloc(sizeof(specialsparse));
	FILE *file;

	g->n=0;
	g->e=0;
	file=fopen(edgelist,"r");
	g->edges=malloc(e1*sizeof(edge));
	while (fscanf(file,"%u %u", &(g->edges[g->e].s), &(g->edges[g->e].t))==2) {//Add one edge
		g->n=max3(g->n,g->edges[g->e].s,g->edges[g->e].t);
		g->e++;
		if (g->e==e1) {
			e1+=NLINKS;
			g->edges=realloc(g->edges,e1*sizeof(edge));
		}
	}
	fclose(file);
	g->n++;

	g->edges=realloc(g->edges,g->e*sizeof(edge));

	return g;
}

//used in qsort
int cmp(void const *p1, void const *p2){
	edge e1 = *((edge*)p1);
	edge e2 = *((edge*)p2);

	if (e1.s < e2.s){
		return -1;
	}
	if (e1.s > e2.s){
		return 1;
	}
	if (e1.t < e2.t){
		return -1;
	}
	return 1;
}

//relabel the edges following the core ordering, souce smaller than target and sort the edges
void relabel(specialsparse *g){
	Edge i;
	Node source, target, tmp;

	for (i=0;i<g->e;i++) {
		source=g->rank[g->edges[i].s];
		target=g->rank[g->edges[i].t];
		if (source<target){
			tmp=source;
			source=target;
			target=tmp;
		}
		g->edges[i].s=source;
		g->edges[i].t=target;
	}
	qsort(g->edges,g->e,sizeof(edge),cmp);

}

// HEAP DATASTRUCTURE TO COMPUTE THE CORE ORDERING

typedef struct {
	Node key;
	Node value;
} keyvalue;

typedef struct {
	Node n_max;	// max number of nodes.
	Node n;	// number of nodes.
	Node *pt;	// pointers to nodes.
	keyvalue *kv; // nodes.
} bheap;

bheap *construct(Node n_max){
	Node i;
	bheap *heap=malloc(sizeof(bheap));

	heap->n_max=n_max;
	heap->n=0;
	heap->pt=malloc(n_max*sizeof(Node));
	for (i=0;i<n_max;i++) heap->pt[i]=-1;
	heap->kv=malloc(n_max*sizeof(keyvalue));
	return heap;
}

inline void swap(bheap *heap,Node i, Node j) {
	keyvalue kv_tmp=heap->kv[i];
	Node pt_tmp=heap->pt[kv_tmp.key];
	heap->pt[heap->kv[i].key]=heap->pt[heap->kv[j].key];
	heap->kv[i]=heap->kv[j];
	heap->pt[heap->kv[j].key]=pt_tmp;
	heap->kv[j]=kv_tmp;
}

inline void bubble_up(bheap *heap,Node i) {
	Node j=(i-1)/2;
	while (i>0) {
		if (heap->kv[j].value>heap->kv[i].value) {
			swap(heap,i,j);
			i=j;
			j=(i-1)/2;
		}
		else break;
	}
}

inline void bubble_down(bheap *heap) {
	Node i=0,j1=1,j2=2,j;
	while (j1<heap->n) {
		j=( (j2<heap->n) && (heap->kv[j2].value<heap->kv[j1].value) ) ? j2 : j1 ;
		if (heap->kv[j].value < heap->kv[i].value) {
			swap(heap,i,j);
			i=j;
			j1=2*i+1;
			j2=j1+1;
			continue;
		}
		break;
	}
}

inline void insert(bheap *heap,keyvalue kv){
	heap->pt[kv.key]=(heap->n)++;
	heap->kv[heap->n-1]=kv;
	bubble_up(heap,heap->n-1);
}

inline void update(bheap *heap,Node key){
	Node i=heap->pt[key];
	if (i!=-1){
		((heap->kv[i]).value)--;
		bubble_up(heap,i);
	}
}

inline keyvalue popmin(bheap *heap){
	keyvalue min=heap->kv[0];
	heap->pt[min.key]=-1;
	heap->kv[0]=heap->kv[--(heap->n)];
	heap->pt[heap->kv[0].key]=0;
	bubble_down(heap);
	return min;
}

//Building the heap structure with (key,value)=(node,degree) for each node
bheap* mkheap(Node n,Node *v){
	Node i;
	keyvalue kv;
	bheap* heap=construct(n);
	for (i=0;i<n;i++){
		kv.key=i;
		kv.value=v[i];
		insert(heap,kv);
	}
	return heap;
}

void freeheap(bheap *heap){
	free(heap->pt);
	free(heap->kv);
	free(heap);
}

// BACK TO THE SPECIAL SPARSE GRAPH DATASTRUCTURE

//computing degeneracy ordering and core value
void ord_core(specialsparse* g){
	Node i,j,r=0,n=g->n;
	keyvalue kv;
	bheap *heap;

	Node *d0=calloc(g->n,sizeof(Node));
	Edge *cd0=malloc((g->n+1)*sizeof(Edge));
	Node *adj0=malloc(2*g->e*sizeof(Node));
	for (i=0;i<g->e;i++) {
		d0[g->edges[i].s]++;
		d0[g->edges[i].t]++;
	}
	cd0[0]=0;
	for (i=1;i<g->n+1;i++) {
		cd0[i]=cd0[i-1]+d0[i-1];
		d0[i-1]=0;
	}
	for (i=0;i<g->e;i++) {
		adj0[ cd0[g->edges[i].s] + d0[ g->edges[i].s ]++ ]=g->edges[i].t;
		adj0[ cd0[g->edges[i].t] + d0[ g->edges[i].t ]++ ]=g->edges[i].s;
	}

	heap=mkheap(n,d0);

	g->rank=malloc(g->n*sizeof(Node));
	//g->map=malloc(g->n*sizeof(unsigned));
	for (i=0;i<g->n;i++){
		kv=popmin(heap);
		g->rank[kv.key]=n-(++r);
		//g->map[n-r]=kv.key;
		for (j=cd0[kv.key];j<cd0[kv.key+1];j++){
			update(heap,adj0[j]);
		}
	}
	freeheap(heap);
	free(d0);
	free(cd0);
	free(adj0);
}

//Building the special graph structure
void mkspecial(specialsparse *g, Kvalue k){
	Edge i;
	Node ns,max;
	Node *d,*sub;
	Kvalue *lab;

	g->k=k;
	d=calloc(g->n,sizeof(Node));

	for (i=0;i<g->e;i++) {
		d[g->edges[i].s]++;
	}

	g->cd=malloc((g->n+1)*sizeof(Edge));
	ns=0;
	g->cd[0]=0;
	max=0;
	sub=malloc(g->n*sizeof(Node));
	lab=malloc(g->n*sizeof(Kvalue));
	for (i=1;i<g->n+1;i++) {
		g->cd[i]=g->cd[i-1]+d[i-1];
		max=(max>d[i-1])?max:d[i-1];
		sub[ns++]=g->n-i;//reverse order instead of "i-1"
		d[i-1]=0;
		lab[i-1]=k;
	}
	printf("max degree = %u\n",max);
	g->max=max;

	g->adj=malloc(g->e*sizeof(Node));

	for (i=0;i<g->e;i++) {
		g->adj[ g->cd[g->edges[i].s] + d[ g->edges[i].s ]++ ]=g->edges[i].t;
	}
	free(g->edges);

	g->ns=malloc((k+1)*sizeof(Node));
	g->ns[k]=ns;

	g->d=malloc((k+1)*sizeof(Node*));
	g->sub=malloc((k+1)*sizeof(Node*));
	for (i=2;i<k;i++){
		g->d[i]=malloc(g->n*sizeof(Node));
		g->sub[i]=malloc(max*sizeof(Node));
	}
	g->d[k]=d;
	g->sub[k]=sub;

	g->lab=lab;
}

//SET DATASTRUCTURE

typedef struct {
	Clique nl;//number of elements in set
	Clique nlmax;//maximum number of element in set
	Clique* list;//elements in set

	Clique ntmax;//size of tab
	Kvalue* tab;//tab[i]==1 iff i is in list
} Set ;

Set* allocset(){
	Set* s=malloc(sizeof(Set));
	s->nl=0;
	s->nlmax=S2MAX;
	s->list=malloc(S2MAX*sizeof(Clique));
	s->ntmax=S2MAX;
	s->tab=calloc(S2MAX,sizeof(Kvalue));
	return s;
}

inline bool isinset(Clique p, Set* s){
	if (p>=s->ntmax){
		return 0;
	}
	return s->tab[p];
}


inline void add2set(Clique p, Set* s){
	if (p>=s->ntmax){
 		s->tab=realloc(s->tab,(p+S2MAX)*sizeof(Kvalue));
		bzero(s->tab+s->ntmax,(p+S2MAX-s->ntmax)*sizeof(Kvalue));
		s->ntmax=p+S2MAX;
	}
	if (s->tab[p]==0){
		s->nl++;
		if (s->nl==s->nlmax){
			s->nlmax*=2;
			s->list=realloc(s->list,s->nlmax*sizeof(Clique));
		}
		s->list[s->nl-1]=p;
	}
	s->tab[p]++;
}

inline void clearset(Set* s){
	Clique i;
	for (i=0;i<s->nl;i++){
		s->tab[s->list[i]]=0;
	}
	s->nl=0;
}

// OVERLAPPING UNIONFIND DATASTRUCTURE

typedef struct {
	char k;//size of the k-cliques to considered

	//to obtain the id of an edge
	Edge e;
	Edge *cd;//cumulative degree: (starts with 0) length=n+1
	Node *adj;//truncated list of neighbors

	//putting edges in sets
	Clique *n1;//n1[i]=number of sets edge i belongs to
	Clique *n1max;//n1max[i]=maximum number of sets edge i belongs to
	Clique **s1;//s1[i]=list of sets that the edge i belongs to

	//plain union find datastructure on the sets of edges:
	Clique n2;//number of sets of sets
	Clique n2max;//maximum number of sets of sets
	Clique *s2;//s2[i]=parent of set of sets i
	unsigned char *r;//r[i]=rank of set of sets i
} unionfind;//overlappingunionfind

unionfind* allocunionfind(specialsparse *g){
	unionfind *ouf=malloc(sizeof(unionfind));

	ouf->k=g->k;
	ouf->e=g->e;
	ouf->cd=g->cd;
	ouf->adj=malloc(g->e*sizeof(Node));//g->adj needs to be copied as permuations occur when listing k-cliques
	memcpy( (void*)ouf->adj, (void*)g->adj, g->e*sizeof(Node) );

	ouf->n1=calloc(ouf->e,sizeof(Clique));
	ouf->n1max=calloc(ouf->e,sizeof(Clique));
	ouf->s1=malloc(ouf->e*sizeof(Clique*));

	ouf->n2=0;
	ouf->n2max=S2MAX;
	ouf->s2=malloc(ouf->n2max*sizeof(Clique));
	ouf->r=malloc(ouf->n2max*sizeof(Kvalue));

	return ouf;
}

inline int cmp2(Node u, Node v){
	if (u < v){
		return -1;
	}
	if (u > v){
		return 1;
	}
	return 0;
}

inline Edge edgeid(edge ed,unionfind* ouf){
	int r;
	Edge first=ouf->cd[ed.s], last=ouf->cd[ed.s+1]-1, middle=(first+last)/2;
	while (1) {
		r=cmp2(ed.t,ouf->adj[middle]);
		if (r==1){
			first=middle+1;
		}
		else if (r==-1){
			last=middle-1;
		}
		else{
			return middle;
		}
		middle = (first+last)/2;
	}
}

Clique Find(Clique x, unionfind *ouf){
	if (ouf->s2[x]!=x){
		ouf->s2[x]=Find(ouf->s2[x],ouf);
	}
	return ouf->s2[x];
}

inline Clique Union(Clique xr, Clique yr, unionfind *ouf){
	if (xr==yr || xr==-1){
		return yr;
	}
	if (ouf->r[xr] < ouf->r[yr]){
		ouf->s2[xr] = yr;
		return yr;
	}
	if (ouf->r[xr] > ouf->r[yr]) {
		ouf->s2[yr] = xr;
		return xr;
	}
	ouf->s2[yr] = xr;
	ouf->r[xr] = ouf->r[xr]+1;
	return xr;
}

inline Clique MakeSet(unionfind *ouf){
	Clique p=(ouf->n2)++;
	if (ouf->n2==ouf->n2max){
		ouf->n2max*=2;
		ouf->s2=realloc(ouf->s2,ouf->n2max*sizeof(Clique));
		ouf->r=realloc(ouf->r,ouf->n2max*sizeof(Kvalue));
	}
	ouf->s2[p]=p;
	ouf->r[p]=0;
	return p;	
}

inline void Add(Edge e,Clique p,unionfind *ouf){
	if (ouf->n1max[e]==0){
		ouf->n1max[e]=S1MAX;
		ouf->s1[e]=malloc(S1MAX*sizeof(Clique));
		ouf->s1[e][0]=p;
		ouf->n1[e]++;
	}
	else {
		if (++(ouf->n1[e])==ouf->n1max[e]){
			ouf->n1max[e]*=2;
			ouf->s1[e]=realloc(ouf->s1[e],ouf->n1max[e]*sizeof(Clique));
		}
		ouf->s1[e][ouf->n1[e]-1]=p;
	}
}

// THE HEART OF THE CODE: iterating over k-cliques and computing k-clique communities on the fly.

//merging k-clique communities sharing many edges with the k-clique "cknode"
void mkcoms(Node* cknode,unionfind *ouf){
	Kvalue a,b,c,d,k=ouf->k;
	Edge e;
	edge ed;
	Clique i,p,q;

	static Edge* id=NULL;
	static Set* set1=NULL;
	static Set* set2=NULL;

	if (id==NULL){
		id=malloc(((k*(k-1))/2)*sizeof(Edge));
		set1=allocset();
		set2=allocset();
	}
	c=0;
	for (a=0;a<k;a++) {
		for (b=a+1;b<k;b++) {
			ed.s=cknode[b];
			ed.t=cknode[a];
			id[c++]=edgeid(ed,ouf);
		}
	}
	p=-1;
	for (d=0;d<k;d++) {//node d removed from k-clique
		c=0;
		for (a=0;a<k;a++) {
			if (a!=d){
				for (b=a+1;b<k;b++) {
				  if (b!=d){
						e=id[c];
						for (i=0;i<ouf->n1[e];i++){
							q=Find(ouf->s1[e][i],ouf);
							if (isinset(q,set1)==0){
								add2set(q,set1);
								add2set(q,set2);
							}
							else{//swapping entry i with last one and delete it
								ouf->s1[e][i--]=ouf->s1[e][--(ouf->n1[e])];
							}
						}
						clearset(set1);
					}
					c++;
				}
			}
			else{
				c+=k-a-1;
			}
		}
		for (i=0;i<set2->nl;i++){
			q=set2->list[i];
			if (set2->tab[q]==((k-1)*(k-2))/2){
				p=Union(p,q,ouf);
			}
		}
		clearset(set2);
	}
	if (p==-1){
		p=MakeSet(ouf);
	}
	for (a=0;a<c;a++) {
		Add(id[a],p,ouf);
	}
}

//gives a pass on the k-cliques, calling mkcoms each time a clique is found
void kclique(Kvalue l, specialsparse *g, Node *cknode, Node *cknode2, unionfind *ouf, Clique *n) {
	Node i,i2,u,v,w;
	Edge j,end;
	if(l==2){
		for(i=0; i<g->ns[2]; i++){//list all edges
			u=g->sub[2][i];
			cknode[1]=u;//g->map[u];
			end=g->cd[u]+g->d[2][u];
			for (j=g->cd[u];j<end;j++) {
				(*n)++;
				cknode[0]=g->adj[j];//g->map[g->adj[j]];
				//qsort(cknode,k,sizeof(Node),cmp);//k-cliques already sorted
				mkcoms(cknode,ouf);
			}
		}
		return;
	}

	for(i=0; i<g->ns[l]; i++){
		u=g->sub[l][i];
		cknode[l-1]=u;//g->map[u];
		g->ns[l-1]=0;
		end=g->cd[u]+g->d[l][u];
		for (j=g->cd[u];j<end;j++){//relabeling nodes and forming U'.
			v=g->adj[j];
			if (g->lab[v]==l){
				g->lab[v]=l-1;
				g->sub[l-1][g->ns[l-1]++]=v;
				g->d[l-1][v]=0;//new degrees
			}
		}
		for (i2=0;i2<g->ns[l-1];i2++){//reodering adjacency list and computing new degrees
			v=g->sub[l-1][i2];
			end=g->cd[v]+g->d[l][v];
			for (j=g->cd[v];j<end;j++){
				w=g->adj[j];
				if (g->lab[w]==l-1){
					g->d[l-1][v]++;
				}
				else{
					g->adj[j--]=g->adj[--end];
					g->adj[end]=w;
				}
			}
		}

		kclique(l-1, g, cknode, cknode2, ouf, n);

		for (i2=0;i2<g->ns[l-1];i2++){//restoring labels
			v=g->sub[l-1][i2];
			g->lab[v]=l;
		}

	}
}

int main(int argc,char** argv){
	specialsparse* g;
	Kvalue k=atoi(argv[1]);
	Node *cknode=malloc(k*sizeof(unsigned)),*cknode2=malloc(k*sizeof(unsigned));
	Clique i,n;
	unionfind *ouf;

	time_t t0,t1,t2;
	t1=time(NULL);
	t0=t1;

	printf("Reading edgelist from file %s\n",argv[2]);

	g=readedgelist(argv[2]);
	printf("Number of nodes = %u\n",g->n);
	printf("Number of edges = %lu\n",g->e);

	t2=time(NULL);
	printf("- Time = %ldh%ldm%lds\n",(t2-t1)/3600,((t2-t1)%3600)/60,((t2-t1)%60));
	t1=t2;

	printf("Building the graph structure\n");

	ord_core(g);
	relabel(g);

	mkspecial(g,k);

	printf("Number of nodes = %u\n",g->n);
	printf("Number of edges = %lu\n",g->e);

	t2=time(NULL);
	printf("- Time = %ldh%ldm%lds\n",(t2-t1)/3600,((t2-t1)%3600)/60,((t2-t1)%60));
	t1=t2;

	printf("Building overlapping unionfind datastructure\n");
	ouf=allocunionfind(g);

	printf("Iterating over all %u-cliques\n",k);

	n=0;
	kclique(k, g, cknode, cknode2, ouf, &n);

	printf("Number of %u-cliques = %llu\n",k,n);

	t2=time(NULL);
	printf("- Time = %ldh%ldm%lds\n",(t2-t1)/3600,((t2-t1)%3600)/60,((t2-t1)%60));
	t1=t2;

	n=0;
	for (i=0;i<ouf->n2;i++){
		if (ouf->s2[i]==i){
			n++;
		}
	}
	printf("Number of %u-clique communities = %llu\n",k,n);

	freespecialsparse(g);

	printf("- Overall time = %ldh%ldm%lds\n",(t2-t0)/3600,((t2-t0)%3600)/60,((t2-t0)%60));

	return 0;
}

