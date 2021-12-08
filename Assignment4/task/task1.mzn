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

% --------------------------------
% Maximum amount of cycles it can take. N = number of operations, and since del_mul > del_add, we multiply by del_mul
int: maxCycles = n*del_mul;

% Create an array of 0..maxCycles
array[1..n] of var 0..maxCycles : s;

% Create an array of total costs of the operations
array[1..n] of var 1..del_mul : total = [if i in mul then del_mul else del_add endif | i in 1..n];

% Get the length of no_adds and no_muls
int: no_adds = length(set2array(add));
int: no_muls = length(set2array(mul));

% Create arrays of s_adds and s_muls to keep track of the start times of the respective operations
array[1..no_adds] of var 0..maxCycles: s_adds = [s[i] | i in 1..n where i in add];
array[1..no_muls] of var 0..maxCycles: s_muls = [s[i] | i in 1..n where i in mul];

% Check that the total time plus the execution time is less than the dependancy time
constraint
  forall(i in 1..n)(
  	  forall(dep in dependencies[i]) (
  		   total[i] + s[i] <= s[dep]
    )
  );

array[1..no_adds] of var 0..del_add: d_add = [del_add | i in 1..no_adds];
array[1..no_muls] of var 0..del_mul: d_mul = [del_mul | i in 1..no_muls];
array[1..no_adds] of var 0..1: r_add = [1 | i in 1..no_adds];
array[1..no_muls] of var 0..1: r_mul = [1 | i in 1..no_muls];
var int: cost = max([s[l] + total[l] | l in last]);

% Input: 
% array[int] of var int: s --> start times // 
% array[int] of var int: d, --> durations
% array[int] of var int: r,  -> resource requirements
% var int: b --> global resource bound (number_add / number_mul)
constraint cumulative(s_adds, d_add, r_add, number_add); % Cumulative add
constraint cumulative(s_muls, d_mul, r_mul, number_mul); % Cumulative mul

solve minimize cost;

output([
  "Strt: ", show(s_adds),
  "Strt: ", show(s_muls),
  "Strt: ", show(cost)
]);