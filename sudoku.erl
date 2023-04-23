-module(sudoku).
%-include_lib("eqc/include/eqc.hrl").
-compile(export_all).

%% %% generators

%% matrix(M,N) ->
%%     vector(M,vector(N,nat())).

%% matrix transpose: using list comprehension
transpose([Row]) ->
    [[X] || X <- Row];
transpose([Row|M]) ->
    [[X|Xs] || {X,Xs} <- lists:zip(Row,transpose(M))].

%% prop_transpose() ->
%%     ?FORALL({M,N},{nat(),nat()},
%% 	    ?FORALL(Mat,matrix(M+1,N+1),
%% 		    transpose(transpose(Mat)) == Mat)).

%% map a matrix to a list of 3x3 blocks, each represented by the list
%% of elements in row order

%% triples takes list and groups into goups of 3
triples([A,B,C|D]) ->
    [[A,B,C]|triples(D)];
triples([]) ->
    [].
 
%% uses triples to from matrix -> 3x3 blocks
blocks(M) ->
    Blocks = [triples(X) || X <- transpose([triples(Row) || Row <- M])],
    lists:append(
      lists:map(fun(X)->
			lists:map(fun lists:append/1, X)
		end,
		Blocks)).

unblocks(M) ->
    lists:map(
      fun lists:append/1,
      transpose(
	lists:map(
	  fun lists:append/1,
	  lists:map(
	    fun(X)->lists:map(fun triples/1,X) end,
	    triples(M))))).

%% prop_blocks() ->
%%     ?FORALL(M,matrix(9,9),
%% 	    unblocks(blocks(M)) == M).

%% decide whether a position is safe

%% takes a row of a Sudoku grid and returns a list of its entries (i.e., the digits that appear in the row)
entries(Row) ->
    [X || X <- Row,
	  1 =< X andalso X =< 9].

%%  takes a row of a Sudoku grid and returns true if the row is "safe", meaning that it contains no repeated digits.
safe_entries(Row) ->
    Entries = entries(Row),
    lists:sort(Entries) == lists:usort(Entries).

%% Sudoku grid and returns true if all of its rows are safe.
safe_rows(M) ->
    lists:all(fun safe_entries/1,M).

%%  takes a Sudoku grid and returns true if the grid is safe (i.e., if all of its rows, columns, and blocks are safe).
safe(M) ->
    safe_rows(M) andalso
	safe_rows(transpose(M)) andalso
	safe_rows(blocks(M)).

%% fill blank entries with a list of all possible values 1..9
fill(M) ->
    Nine = lists:seq(1,9),
    [[if 1=<X, X=<9 ->
	      X;
	 true ->
	      Nine
      end
      || X <- Row]
     || Row <- M].

%% refine entries which are lists by removing numbers they are known
%% not to be

%%takes a Sudoku grid and repeatedly applies the refine_rows function to it until no further changes can be made. 
refine(M) ->
    NewM = refine_rows(
	  transpose(
	    refine_rows(
	      transpose(
		unblocks(
		  refine_rows(
		    blocks(M))))))),
    if M==NewM ->
	    M;
       true ->
	    refine(NewM)
    end.

refine_rows(M) ->
    lists:map(fun refine_row/1,M).
  
%% takes a Sudoku grid and applies the refine_row function to each row, which updates any list of possible values for an empty cell by removing any values that are not possible based on the contents of the row, column, and block that the cell is in
refine_row(Row) ->
    Entries = entries(Row),
    NewRow =
	[if is_list(X) ->
		 case X--Entries of
		     [] ->
			 exit(no_solution);
		     [Y] ->
			 Y;
		     NewX ->
			 NewX
		 end;
	    true ->
		 X
	 end
	 || X <- Row],
    NewEntries = entries(NewRow),
    %% check we didn't create a duplicate entry
    case length(lists:usort(NewEntries)) == length(NewEntries) of
	true ->
	    NewRow;
	false ->
	    exit(no_solution)
    end.

is_exit({'EXIT',_}) ->
    true;
is_exit(_) ->
    false.

%% is a puzzle solved?
%%  takes a Sudoku grid and returns true if it is a valid solution
solved(M) ->
    lists:all(fun solved_row/1,M).

solved_row(Row) ->
    lists:all(fun(X)-> 1=<X andalso X=<9 end, Row).

%% how hard is the puzzle? takes a Sudoku grid and returns a score indicating how difficult the puzzle is to solve
hard(M) ->		      
    lists:sum(
      [lists:sum(
	 [if is_list(X) ->
		  length(X);
	     true ->
		  0
	  end
	  || X <- Row])
       || Row <- M]).

%% choose a position {I,J,Guesses} to guess an element, with the
%% fewest possible choices

guess(M) ->
    Nine = lists:seq(1,9),
    {_,I,J,X} =
	lists:min([{length(X),I,J,X}
		   || {I,Row} <- lists:zip(Nine,M),
		      {J,X} <- lists:zip(Nine,Row),
		      is_list(X)]),
    {I,J,X}.

%% given a matrix, guess an element to form a list of possible
%% extended matrices, easiest problem first.

guesses(M) ->
    {I,J,Guesses} = guess(M),
    % Ms = case hard(M) >= 275 of
    %          true ->
    %              io:format("hard: ~p~n",[hard(M)]),
    %              pmap(fun(X) -> catch refine(update_element(M,I,J,X)) end, Guesses);
    %          false ->
    %              [catch refine(update_element(M,I,J,G)) || G <- Guesses]
    %      end,
    Ms = [catch refine(update_element(M,I,J,G)) || G <- Guesses],
    SortedGuesses =
	    lists:sort(
	      [{hard(NewM),NewM}
	    || NewM <- Ms,
	       not is_exit(NewM)]),
    [G || {_,G} <- SortedGuesses].

%%  takes a Sudoku grid and the position of an empty cell and a value to fill it with, and returns a new grid with the cell filled in.c(
update_element(M,I,J,G) ->
    update_nth(I,update_nth(J,G,lists:nth(I,M)),M).

update_nth(I,X,Xs) ->
    {Pre,[_|Post]} = lists:split(I-1,Xs),
    Pre++[X|Post].

%% prop_update() ->
%%     ?FORALL(L,list(int()),
%% 	    ?IMPLIES(L/=[],
%% 		     ?FORALL(I,choose(1,length(L)),
%% 			     update_nth(I,lists:nth(I,L),L) == L))).

%% solve a puzzle

solve(M) ->
    Solution = solve_refined(M),
    % Solution = solve_refined(refine(fill(M))),
    case valid_solution(Solution) of
	true ->
	    Solution;
	false ->
	    exit({invalid_solution,Solution})
    end.

solve_refined(M) ->
  case solved(M) of 
	true ->
	    M;
	false ->
	    solve_one(guesses(M))
    end.

solve_one([]) ->
    exit(no_solution);
solve_one([M]) ->
    solve_refined(M);
solve_one([M|Ms]) ->
    case catch solve_refined(M) of
	{'EXIT', no_solution} ->
	    solve_one(Ms);
	Solution ->
	    Solution
    end.

%% benchmarks

-define(EXECUTIONS,100).

bm(F) ->
    {T,_} = timer:tc(?MODULE,repeat,[F]),
    T/?EXECUTIONS/1000.

repeat(F) ->
    [F() || _ <- lists:seq(1,?EXECUTIONS)].

benchmarks(Puzzles) ->
    [{Name,bm(fun()->solve_top(M) end)} || {Name,M} <- Puzzles].

benchmarks() ->
  {ok,Puzzles} = file:consult("problems.txt"),
  timer:tc(?MODULE,benchmarks,[Puzzles]).


pbenchmarks(Puzzles) ->
    pmap(fun({Name, M}) -> {Name, bm(fun() -> solve(M) end)} end, Puzzles).


pmap(F, L) ->
    Parent = self(),
    Mapper = fun(X) ->
        spawn_link(fun() ->
            try
                Result = F(X),
                Parent ! {self(), {ok, Result}}
            catch
                _:_ ->
                    Parent ! {self(), {error, no_solution}}
            end
        end)
    end,
    Pids = [Mapper(X) || X <- L],
    [receive
        {Pid, {ok, Result}} ->
            Result;
        {Pid, {error, Reason}} ->
            {'EXIT', Reason}
     end || Pid <- Pids].

%% check solutions for validity

valid_rows(M) ->
    lists:all(fun valid_row/1,M).

valid_row(Row) ->
    lists:usort(Row) == lists:seq(1,9).

valid_solution(M) ->
    valid_rows(M) andalso valid_rows(transpose(M)) andalso valid_rows(blocks(M)).

%%%%%%%%%%%% Pool %%%%%%%%%%%%%%%%%

solve_top(M) ->
  Refined = refine(fill(M)),
  case hard(Refined) >= 200 of
    true ->
      pool_solve(Refined);
    false ->
      solve(Refined)
  end.


pool_solve(M) ->
    start_pool(erlang:system_info(schedulers)-1),
    Parent = self(),
    _ = spawn_link(fun() -> pool_solve_refined(M, Parent) end),
    % _ = spawn_link(fun() -> pool_solve_refined(refine(fill(M)), Parent) end),
    receive
        {found_solution, Solution} ->
            pool ! {stop, self()},
            receive {pool, stopped} -> ok end,
            case valid_solution(Solution) of
                true ->
                    Solution;
                false ->
                    exit({invalid_solution, Solution})
            end
    end.

pool_solve_refined(M, P) ->
    case solved(M) of
        true ->
          P ! {found_solution, M},
          ok;
        false ->
          solve_one_pool(guesses(M), P),
          ok
    end.

solve_one_pool(Ms, P) ->
    Specs = [speculate_on_worker(fun() -> pool_solve_refined(M, P) end) || M <- Ms],
    Diff = lists:sum(lists:map(fun(M) -> hard(M) end, Ms)),
    if Diff >= 300 ->
           io:format("Diff: ~p~n", [Diff]),
           _ = pmap(fun(S) -> par_wait_for_solution(S) end, Specs),
           exit(no_solution);
       true ->
           _ = wait_for_solution(Specs, P),
           ok
    end.
    %_ = wait_for_solution(Specs, P),
    %_ = pmap(fun(S) -> par_wait_for_solution(S) end, Specs),

par_wait_for_solution(S) ->
  case (catch worker_value_of(S)) of
    {'EXIT', no_solution} ->
      ok; 
    Idk ->
      ok
    end.

wait_for_solution([], _P) ->
    exit(no_solution);

wait_for_solution([S | Specs], P) ->
  case (catch worker_value_of(S)) of
    {'EXIT', no_solution} ->
      wait_for_solution(Specs, P);
    Idk ->
      ok
    end.



start_pool(N) ->
  true = register(pool,spawn_link(fun()->pool([worker() || _ <- lists:seq(1,N)])
end)).

pool(Workers) ->
  pool(Workers,Workers).

pool(Workers,All) ->
  receive
    {get_worker,Pid} ->
      case Workers of
        [] ->
          Pid ! {pool,no_worker},
          pool(Workers,All);
        [W|Ws] ->
          Pid ! {pool,W},
          pool(Ws,All)
      end;
    {return_worker,W} ->
      pool([W|Workers],All);
    {stop,Pid} ->
      [unlink(W) || W <- All],
      [exit(W,kill) || W <- All],
      unregister(pool),
      Pid ! {pool,stopped}
   end.

worker() ->
  spawn_link(fun work/0).

work() ->
  receive
    {task,Pid,R,F} ->
      try
        Res = F(),
        Pid ! {R, Res},
        try
          pool ! {return_worker,self()}
        catch
          error:Reason ->
            io:format("Error returning worker to pool: ~p~n", [Reason])
        end
      catch
        _:_ ->
          Pid ! {R, {error, no_solution}},
          try
            pool ! {return_worker,self()}
          catch
            error:R2 ->
              io:format("Error returning worker to pool: ~p~n", [R2])
          end
      end,
      work()
   end.

speculate_on_worker(F) ->
  case whereis(pool) of
    undefined ->
      ok; %% we're stopping
    Pool -> Pool ! {get_worker,self()}
   end,
   receive
    {pool,no_worker} ->
      {not_speculating,F};
    {pool,W} ->
      R = make_ref(),
      W ! {task,self(),R,F},
      {speculating,R}
   end.

worker_value_of({not_speculating,F}) ->
  F();
worker_value_of({speculating,R}) ->
  receive
    {R,ok} ->
      ok;
    {R,{error, Reason}} ->
      exit(no_solution)
  end.
