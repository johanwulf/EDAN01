include "globals.mzn";

% Inputs
int: graph_size;
int: start;
int: n_dests;
array[int] of int: dest;
int: n_edges;
array[int] of int: from;
array[int] of int: to;
array[int] of int: cost;

% Adjecency matrix
array[1..n_edges*2] of var set of int: allEdges;
constraint forall(i in 1..n_edges) (allEdges[i] = {from[i], to[i]} /\ allEdges[i+n_edges] = {to[i], from[i]});


%array[1..n_edges, 1..2] of int: x = array2d(1..n_edges, 1..2, [from[i] | i in 1..n_edges, j in 1..2 where i<j ]);

array[1..n_edges, 1..2] of int: arcs = array2d(1..n_edges, 1..2, 
  [1, 2] ++
  [1, 3] ++
  [2, 3] ++
  [2, 4] ++
  [3, 5] ++
  [4, 5] ++
  [4, 6]);

array[1..graph_size] of int: balances = [1, 0, 0, 0, 0, -1];
array[1..n_edges] of var 0..1: flows;
array[1..n_edges] of var 0..max(cost): flows2;
constraint network_flow(arcs, balances, flows);

constraint forall(i in 1..n_edges) (if flows[i] == 1 then flows2[i] = cost[i] endif);
var int: sum = sum(flows2);

output[show(allEdges)];
%output[show(s)];

solve minimize sum;