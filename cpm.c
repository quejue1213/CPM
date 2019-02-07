/*
Info:
Feel free to use these lines as you wish.
This program stores (k-1)-cliques in memory and computes k-clique communities such as defined by Palla et al.

To compile:
"gcc cpm.c -O9 -o cpm".

To execute:
"./cpmAPPROX k edgelist.txt".
- k >= 3
- "edgelist.txt" should contain the graph: one edge on each line separated by a space (no self-loop or multiple edge please).
Will print the number of k-cliques and the number of k-clique communities.
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>

#define NLINKS 100000000 //maximum number of edges for memory allocation, will increase if needed

typedef unsigned int Node;
typedef unsigned long int Edge;
typedef unsigned long long int Clique;
typedef unsigned char Kvalue;


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

}

///// CORE ordering /////////////////////

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

void swap(bheap *heap,Node i, Node j) {
	keyvalue kv_tmp=heap->kv[i];
	Node pt_tmp=heap->pt[kv_tmp.key];
	heap->pt[heap->kv[i].key]=heap->pt[heap->kv[j].key];
	heap->kv[i]=heap->kv[j];
	heap->pt[heap->kv[j].key]=pt_tmp;
	heap->kv[j]=kv_tmp;
}

void bubble_up(bheap *heap,Node i) {
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

void bubble_down(bheap *heap) {
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

void insert(bheap *heap,keyvalue kv){
	heap->pt[kv.key]=(heap->n)++;
	heap->kv[heap->n-1]=kv;
	bubble_up(heap,heap->n-1);
}

void update(bheap *heap,Node key){
	Node i=heap->pt[key];
	if (i!=-1){
		((heap->kv[i]).value)--;
		bubble_up(heap,i);
	}
}

keyvalue popmin(bheap *heap){
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

//////////////////////////
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
		sub[ns++]=i-1;
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

//modify the "special" datastructure: "k=k+1"
void remkspecial(specialsparse *g){
	Node i;
	Kvalue k=g->k+1;
	g->k=k;
	for (i=0;i<g->n;i++) {
		g->lab[i]=k;
	}
	g->ns=realloc(g->ns,(k+1)*sizeof(Node));
	g->ns[k]=g->ns[k-1];
	g->d=realloc(g->d,(k+1)*sizeof(Node*));
	g->sub=realloc(g->sub,(k+1)*sizeof(Node*));
	g->d[k]=g->d[k-1];
	g->d[k-1]=malloc(g->n*sizeof(Node));
	g->sub[k]=g->sub[k-1];
	g->sub[k-1]=malloc(g->max*sizeof(Node));
}


void countck(Kvalue l, specialsparse *g, Clique *n) {
	Node i,u,v,w;
	Edge j,end,q;

	if(l==2){
		for(i=0; i<g->ns[2]; i++){//list all edges
			(*n)+=g->d[2][g->sub[2][i]];
		}
		return;
	}

	for(i=0; i<g->ns[l]; i++){
		u=g->sub[l][i];
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
		for (j=0;j<g->ns[l-1];j++){//reodering adjacency list and computing new degrees
			v=g->sub[l-1][j];
			end=g->cd[v]+g->d[l][v];
			for (q=g->cd[v];q<end;q++){
				w=g->adj[q];
				if (g->lab[w]==l-1){
					g->d[l-1][v]++;
				}
				else{
					g->adj[q--]=g->adj[--end];
					g->adj[end]=w;
				}
			}
		}

		countck(l-1, g, n);

		for (j=0;j<g->ns[l-1];j++){//restoring labels
			v=g->sub[l-1][j];
			g->lab[v]=l;
		}

	}
}



typedef struct {
	Clique n;//number of k-cliques
	Kvalue k;//value of k
	Node **c;//c[i]=pointer to iest k-clique
	Node *tab;//storing the k-cliques
	Clique *p;//parents
	unsigned char *r;//ranks
} unionfind;


unionfind* allocunionfind(specialsparse *g){
	unionfind *uf=malloc(sizeof(unionfind));
	Node i;
	Clique n=0;
	Kvalue k=g->k;

	countck(k, g, &n);
	uf->n=n;
	uf->k=k;
	uf->c=malloc(n*sizeof(Node*));
	uf->tab=malloc(n*k*sizeof(Node));
	uf->p=malloc(n*sizeof(Clique));
	uf->r=malloc(n*sizeof(unsigned char));
	for (i=0;i<n;i++){
		uf->c[i]=uf->tab+i*k;
		uf->p[i]=-1;//NULL
		uf->r[i]=0;
	}

	return uf;
}



/*
//for future use in qsort
int cmp (const void * a, const void * b){
	if (*(Node*)a>*(Node*)b){
		return 1;
	}
	return -1;
}
*/

void mkunionfind(Kvalue l, specialsparse *g, Node *cknode, unionfind *uf,Clique *n) {
	Node i;
	Edge j,q,end,u,v,w;
	Kvalue a,k=g->k;

	if(l==2){
		for(i=0; i<g->ns[2]; i++){//list all edges
			u=g->sub[2][i];
			cknode[1]=u;//g->map[u];
			end=g->cd[u]+g->d[2][u];
			for (j=g->cd[u];j<end;j++) {
				cknode[0]=g->adj[j];//g->map[g->adj[j]];
				//qsort(cknode,k,sizeof(Node),cmp);//k-cliques already sorted
				for (a=0;a<k;a++){
					uf->tab[(*n)*k+a]=cknode[a];
				}
				(*n)++;
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
		for (j=0;j<g->ns[l-1];j++){//reodering adjacency list and computing new degrees
			v=g->sub[l-1][j];
			end=g->cd[v]+g->d[l][v];
			for (q=g->cd[v];q<end;q++){
				w=g->adj[q];
				if (g->lab[w]==l-1){
					g->d[l-1][v]++;
				}
				else{
					g->adj[q--]=g->adj[--end];
					g->adj[end]=w;
				}
			}
		}

		mkunionfind(l-1, g,cknode, uf, n);

		for (j=0;j<g->ns[l-1];j++){//restoring labels
			v=g->sub[l-1][j];
			g->lab[v]=l;
		}

	}
}

//For futur use in qsort_r. lexicographic sort for cliques
int cmp2(void const *p_i, void const *p_j, unsigned k){
	Kvalue u;
	Node *ci = *((Node**)p_i);
	Node *cj = *((Node**)p_j);

	for (u=0;u<k;u++){
		if (ci[u] < cj[u]){
			return -1;
		}
		else if (ci[u] > cj[u]){
			return 1;
		}
	}
	return 0;
}

int cmp3(Node *c1, Node *c2, Kvalue k){
	Node u;
	for (u=0;u<k;u++){
		if (c1[u] < c2[u]){
			return -1;
		}
		else if (c1[u] > c2[u]){
			return 1;
		}
	}
	return 0;
}

inline Clique cliqueid(Node *ck,unionfind *uf){
	int v;
	Clique first=0, last=uf->n-1, middle=last/2;
	while (1) {
		v=cmp3(ck,uf->c[middle],uf->k);
		if (v==1){
			first=middle+1;
		}
		else if (v==-1){
         		last=middle-1;
		}
		else{
			return middle;
		}
		middle = (first+last)/2;
	}
}

Clique Find(Clique x, unionfind *uf){
	if (uf->p[x]!=x){
		uf->p[x]=Find(uf->p[x],uf);
	}
	return uf->p[x];
}

Clique FindOrCreate(Clique i,unionfind *uf){
	if (uf->p[i]==-1){
		uf->p[i]=i;
		return i;
	}
	return Find(i,uf);
}

Clique Union(Clique xr, Clique yr, unionfind *uf){
	if (xr==yr || xr==-1){
		return yr;
	}
	if (uf->r[xr] < uf->r[yr]){
     		uf->p[xr] = yr;
		return yr;
	}
	if (uf->r[xr] > uf->r[yr]) {
		uf->p[yr] = xr;
		return xr;
	}
	uf->p[yr] = xr;
	uf->r[xr] = uf->r[xr]+1;
	return xr;
}


void kclique(Kvalue l, specialsparse *g, Node *cknode, Node *cknode2, unionfind *uf, Clique *n) {
	Node i,i2,u,v,w;
	Edge j,end;
	Kvalue a,b,c,k=g->k;
	Clique p,q,id;
	if(l==2){
		for(i=0; i<g->ns[2]; i++){//list all edges
			u=g->sub[2][i];
			cknode[1]=u;//g->map[u];
			end=g->cd[u]+g->d[2][u];
			for (j=g->cd[u];j<end;j++) {
				(*n)++;
				cknode[0]=g->adj[j];//g->map[g->adj[j]];
				//qsort(cknode,k,sizeof(Node),cmp);//k-cliques already sorted
				p=-1;
				for (a=0;a<k;a++) {
					c=0;
					for (b=0;b<k;b++) {
						if (b!=a){
							cknode2[c++]=cknode[b];
						}
					}
					id=cliqueid(cknode2,uf);//////////////////////////
					q=FindOrCreate(id,uf);//////////////////////////
					p=Union(p,q,uf);//////////////////////////
				}
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

		kclique(l-1, g, cknode, cknode2, uf, n);

		for (i2=0;i2<g->ns[l-1];i2++){//restoring labels
			v=g->sub[l-1][i2];
			g->lab[v]=l;
		}

	}
}

int main(int argc,char** argv){
	specialsparse* g;
	Kvalue k=atoi(argv[1]);
	Node i;
	Node *cknode=malloc(k*sizeof(unsigned)),*cknode2=malloc(k*sizeof(unsigned));
	Clique n;
	unionfind *uf;

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

	mkspecial(g,k-1);

	printf("Number of nodes = %u\n",g->n);
	printf("Number of edges = %lu\n",g->e);

	t2=time(NULL);
	printf("- Time = %ldh%ldm%lds\n",(t2-t1)/3600,((t2-t1)%3600)/60,((t2-t1)%60));
	t1=t2;

	printf("Building unionfind field with %u-cliques\n",k-1);
	uf=allocunionfind(g);
	n=0;
	mkunionfind(k-1, g, cknode2, uf, &n);
	qsort_r(uf->c,uf->n,sizeof(Clique*),cmp2,k-1);//sorting k-cliques in lexicographic order

	printf("number of %u-cliques = %llu\n",k-1,n);

	remkspecial(g);

	n=0;
	kclique(k, g, cknode, cknode2, uf, &n);

	printf("Number of %u-cliques = %llu\n",k,n);

	t2=time(NULL);
	printf("- Time = %ldh%ldm%lds\n",(t2-t1)/3600,((t2-t1)%3600)/60,((t2-t1)%60));
	t1=t2;

	n=0;
	for (i=0;i<uf->n;i++){
		if (uf->p[i]==i){
			n++;
		}
	}
	printf("Number of %u-clique communities = %llu\n",k,n);

	freespecialsparse(g);

	printf("- Overall time = %ldh%ldm%lds\n",(t2-t0)/3600,((t2-t0)%3600)/60,((t2-t0)%60));

	return 0;
}
