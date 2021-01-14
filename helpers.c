//Hash
FILE *inp = fopen("input.txt", "r");
int n, m;
fscanf(inp, "%d%d", &n, &m);
char buff[256];
HSI name_to_id = hsi_create();
int id = 0;
char **id_to_name = calloc(n, sizeof(char *));
for (int i = 0; i < n; ++i)
{
    fscanf(inp, "%s", buff);
    // hash buff to value id
    hsi_add(name_to_id, buff, id);
    // save buff in id_to_name
    id_to_name[id++] = strdup(buff);
}
char job1[256], job2[256];
cgraph_ivec_t edges = cgraph_ivec_create();
for (int i = 0; i < m; ++i)
{
    fscanf(inp, "%s %s", job1, job2);
    int *j1, *j2;
    // save the pointer to job1 in j1
    hsi_get(name_to_id, job1, &j1);
    hsi_get(name_to_id, job2, &j2);
    cgraph_ivec_push_back(&edges, *j1);
    cgraph_ivec_push_back(&edges, *j2);
}

cgraph_t g;
cgraph_create(&g, edges, 0, true);
cgraph_ivec_t order = cgraph_ivec_create();
cgraph_topological_sorting(&g, &order, CGRAPH_OUT);
FILE *out = fopen("output.txt", "w");
if (cgraph_ivec_size(order) < n)
{
    fprintf(out, "-1");
}
else
{
    for (int i = 0; i < cgraph_ivec_size(order); ++i)
    {
        fprintf(out, "%s\n", id_to_name[order[i]]);
    }
}
fclose(out);
cgraph_destroy(&g);
for (int i = 0; i < n; ++i)
{
    free(id_to_name[i]);
}
free(id_to_name);
cgraph_ivec_free(&edges);
cgraph_ivec_free(&order);
fclose(inp);
return0;

// BFS SIMPLE
int cgraph_simple_bfs(const cgraph_t *graph,
               CGRAPH_INTEGER root,
               cgraph_neimode_t mode,
               bool unreachable,
               cgraph_ivec_t *father,
               cgraph_ivec_t *dist) {
  return cgraph_bfs(graph,
      root,
      mode,
      unreachable,
      0,
      0,
      0,
      father,
      0,
      0,
      dist);
}

//BFS
int cgraph_bfs(const cgraph_t *graph,
               CGRAPH_INTEGER root, // id or vertex root
               cgraph_neimode_t mode, // CGRAPH_OUT
               bool unreachable, // true if we wanna visit all nodes (even unreachable), false otw
               cgraph_ivec_t const restricted, // ptr to a vt containing vertex id
               cgraph_ivec_t *order, // order of visit stored here
               cgraph_ivec_t *rank, // rank of vertices stored here
               cgraph_ivec_t *father, // id of father node stored here
               cgraph_ivec_t *pred, //id of vertex that was visited before the current one is stored here. If there is no such vertex (the current vertex is the root of a search tree), then -1 is stored.
               cgraph_ivec_t *succ, //id of the vertex that was visited after the current one is stored here. If there is no such vertex (the current one is the last in a search tree), then -1 is stored.
               cgraph_ivec_t *dist) {} //the distance from the root of the current search tree is stored here.

