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

% Create an array of paths
array[1..n_edges, 1..2] of int: arcs = array2d(1..n_edges, 1..2, [
  if j mod 2 == 0 then
    from[i]
  else
    to[i]
  endif
| i in 1..n_edges, j in 1..2 ]);

% Set source to produce n_dests units, and sinks to take -1 unit
array[1..graph_size] of int: balances = [ if i == start then n_dests elseif exists(j in 1..n_dests)(dest[j] == i) then -1 else 0 endif | i in 1..graph_size];

% Instead of creating paths back and forth, we create negative flow due to time
array[1..n_edges] of var -n_dests..n_dests: flows;

% The total cost of the flow
var int: totalCost = sum(i in 1..n_edges)(if flows[i] != 0 then cost[i] else 0 endif);

constraint network_flow(arcs, balances, flows);

output[show(totalCost)];

solve minimize totalCost;