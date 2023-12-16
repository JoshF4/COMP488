---- MODULE MazeSolver ----

CONSTANTS
    Width, Height, StartX, StartY, GoalX, GoalY;


VARIABLE x, y, path;


\* Define constants for movement directions
North == 1
South == 2
West == 3
East == 4


Init == 
    /\ x = StartX
    /\ y = StartY
    /\ path = <<>>;


Blocked(i, j) == 
    \/ (i = 1 /\ j = 2)  \* Define your blocked cells here
    \/ (i = 2 /\ j = 2)
    \/ (i = 3 /\ j = 2);


Goal ==
    /\ x = GoalX
    /\ y = GoalY;


Move(direction) == 
    /\ CASE direction
       = North => /\ y > 1 /\ ~Blocked(x, y - 1)
                    /\ y' = y - 1
       = South => /\ y < Height /\ ~Blocked(x, y + 1)
                    /\ y' = y + 1
       = West  => /\ x > 1 /\ ~Blocked(x - 1, y)
                    /\ x' = x - 1
       = East  => /\ x < Width /\ ~Blocked(x + 1, y)
                    /\ x' = x + 1
       = OTHER => /\ FALSE  \* Invalid direction
    /\ path' = Append(path, direction);

Next ==
    \/ Goal
    \/ \E direction \in {North, South, West, East} : Move(direction);


Spec == Init /\ [][Next]_<<x, y, path>> 

Safety ==
    \A i \in 1..(Len(path) - 1) : 
        \/ (path[i] = North /\ ~Blocked(x, y - 1))
        \/ (path[i] = South /\ ~Blocked(x, y + 1))
        \/ (path[i] = West  /\ ~Blocked(x - 1, y))
        \/ (path[i] = East  /\ ~Blocked(x + 1, y));


Termination ==
    \/ Goal
    \/ \E direction \in {North, South, West, East} : 
        /\ x = GoalX
        /\ y = GoalY
        /\ path' = Append(path, direction)
        /\ ~Blocked(x', y');


SpecWithSafety == Spec /\ Safety /\ Termination

\* Uncomment the following line to run model checking
\* \* THEOREM SpecWithSafety => WF_vars(Next, <<x, y, path>>)
