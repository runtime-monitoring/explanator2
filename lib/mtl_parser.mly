/*******************************************************************
 *     This is part of Explanator2, it is distributed under the    *
 *     terms of the GNU Lesser General Public License version 3    *
 *           (see file LICENSE for more details)                   *
 *                                                                 *
 *  Copyright 2021:                                                *
 *  Dmitriy Traytel (UCPH)                                         *
 *  Leonardo Lima (UCPH)                                           *
 *******************************************************************/

%{
open Interval
open Mtl
%}

%token <string> ATOM
%token <Interval.interval> INTERVAL
%token LOPEN ROPEN
%token FALSE TRUE NEG CONJ DISJ EOF
%token SINCE UNTIL
%token NEXT PREV

%nonassoc INTERVAL
%nonassoc PREV NEXT
%nonassoc SINCE UNTIL
%left DISJ
%left CONJ
%nonassoc NEG

%type <Mtl.formula> formula
%start formula

%%

formula:
| e EOF { $1 }

e:
| LOPEN e ROPEN           { $2 }
| TRUE                    { tt }
| FALSE                   { ff }
| e CONJ e                { conj $1 $3 }
| e DISJ e                { disj $1 $3 }
| NEG e                   { neg $2 }
| ATOM                    { p $1 }
| e SINCE INTERVAL e      { since $3 $1 $4 }
| e SINCE e               { since full $1 $3 }
| e UNTIL INTERVAL e      { until $3 $1 $4 }
| e UNTIL e               { until full $1 $3 }
| NEXT INTERVAL e         { next $2 $3 }
| NEXT e                  { next full $2 }
| PREV INTERVAL e         { prev $2 $3 }
| PREV e                  { prev full $2 }
