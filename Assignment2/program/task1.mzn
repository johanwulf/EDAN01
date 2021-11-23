include "globals.mzn";
%Inputs
int: graph_size;
int: start;
int: n_dests;
array[int] of int: dest;
int: n_edges;
array[int] of int: from;
array[int] of int: to;
array[int] of int: cost;
array[int] of int: newCost = cost++cost;

% Adjecency matrix
array[1..n_edges*2, 1..2] of int: arcs = array2d(1..n_edges*2, 1..2, [
  if j mod 2 == 0 then
    if i > n_edges then
       from[i-n_edges]
    else
       to[i]
    endif
  else
    if i > n_edges then
       to[i-n_edges]
    else
       from[i]
    endif
  endif
| i in 1..n_edges*2, j in 1..2 ]);


array[1..graph_size] of int: balances = [1, 0, 0, 0, 0, -1];
array[1..n_edges*2] of var 0..1: flows;
array[1..n_edges*2] of var 0..max(newCost): totalCost;

constraint network_flow(arcs, balances, flows);

output[show(totalCost)];

constraint forall(i in 1..n_edges*2) (if flows[i] == 1 then totalCost[i] = newCost[i] endif);
var int: sum = sum(totalCost);

solve minimize sum;