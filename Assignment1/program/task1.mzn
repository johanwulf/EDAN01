include "globals.mzn";

% Global variables
int: n; % Number of people
int: n_prefs; % Number of preferences
array [1..n_prefs, 1..2] of var 1..n: prefs; % All preferences

% Other stuff
array [1..n] of var 1..n: position; % Position of each person
array [1..n_prefs] of var 0..1: satisfied; % If preference is satisfied, set to 1
var 0..n_prefs: satisfactions; % Total number of satisfactions

constraint alldifferent(position) /\
           forall(i in 1..n_prefs) (if abs(position[prefs[i,1]]-position[prefs[i,2]]) = 1 then satisfied[i] = 1 else satisfied[i] = 0 endif) /\
           satisfactions = sum(satisfied);

solve :: int_search(position, first_fail, complete) maximize satisfactions;