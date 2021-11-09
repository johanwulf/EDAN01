include "globals.mzn";

% Global variables
int: n; % Number of people
int: n_prefs; % Number of preferences
array [1..n_prefs, 1..2] of var 1..n: prefs; % All preferences

% Other stuff
array [1..n] of var 1..n: position; % Position of each person
array [1..n_prefs] of var 1..n: distance; % If preference is satisfied, set to 1
var 1..n: total;

constraint alldifferent(position) /\
           forall(i in 1..n_prefs) (distance[i]=abs(position[prefs[i,1]]-position[prefs[i,2]])) /\
           total=max(distance);

solve minimize total;