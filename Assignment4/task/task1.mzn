include "globals.mzn";

% Global variables
int : del_add; % Number of cycles to complete addition
int : del_mul; % Number of cycles to complete multiplication
int : number_add; % Number of additioners
int : number_mul; % Number of muxers
int : n; % Number of operations
set of int : last;
set of int : add;
set of int : mul;
array[1..n] of set of int : dependencies;

% Solver
array[1..n] of var 0..n*del_mul : s; % n*del_mul = max possible number of cycles it can takes, since del_mul > del_add
array[1..n] of var 1..del_mul : total = [if i in mul then del_mul else del_add endif | i in 1..n]; % Create an array of the total costs of the operations

int: no_adds = length(set2array(add));
int: no_muls = length(set2array(mul));

array[1..no_adds] of var 0..n*del_mul: s_adds = [s[i] | i in 1..n where i in add];
array[1..no_muls] of var 0..n*del_mul: s_muls = [s[i] | i in 1..n where i in mul];

constraint forall(i in 1..n)(s[i] +total[i] <= end);

% Input: 
% array[int] of var int: s --> start times
% array[int] of var int: d, --> durations
% array[int] of var int: r,  -> resource requirements
% var int: b --> global resource bound (number_add / number_mul)
constraint cumulative(s_adds, d, r, number_add); % Cumulative add
constraint cumulative(s_muls, d, r, number_mul); % Cumulative mul