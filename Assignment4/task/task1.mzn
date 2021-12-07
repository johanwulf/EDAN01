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

% Input: 
% array[int] of var int: s --> start times
% array[int] of var int: d, --> durations
% array[int] of var int: r,  -> resource requirements
% var int: b --> global resource bound (number_add / number_mul)
constraint cumulative(s, d, r, number_add); % Cumulative add
constraint cumulative(s, d, r, number_mul); % Cumulative mul