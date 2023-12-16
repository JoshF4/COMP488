---- ---- MODULE TicketVendingMachine ----
EXTENDS TLC, Naturals

VARIABLES 
    insertedCoins,            \* coins inserted by user in machine as ongoing transaction or cancel to return
    depositedCoins,           \* coins earned and stored from transaction
    totalAvailableTickets     \* numbers of available tickets

vars == << insertedCoins, depositedCoins, totalAvailableTickets >>

TypeOK == insertedCoins \in Nat /\ depositedCoins \in Nat /\ totalAvailableTickets \in Nat

\* make sure the ticket is not soud out
Safety == totalAvailableTickets > 0

Liveness == insertedCoins > 0 ~> insertedCoins = 0

\* condition that makes transaction available
TransactionInProgress == insertedCoins > 0

OnlyDispenseAfterDeposit == TRUE

\* max number of coins that can temprory deposit in the machine
MaxCapacity == 20

\* initial status of the machine
Init == 
    /\ totalAvailableTickets = 20 \* total number of tickets that available in the machine
    /\ depositedCoins = 0 
    /\ insertedCoins = 0

\* deposit coins from temprory deposit to internal machine bank
DepositCoin == 
    /\ insertedCoins < totalAvailableTickets
    /\ insertedCoins' = insertedCoins + 1
    /\ insertedCoins' <= MaxCapacity
    /\ UNCHANGED << depositedCoins, totalAvailableTickets >>

\* deliver the ticket to the customer, when the ticket is purchased by its price
DeliverTicket == 
    /\ TransactionInProgress
    /\ totalAvailableTickets > 0 
    /\ insertedCoins' = insertedCoins - 1
    /\ depositedCoins' = depositedCoins + 1
    /\ totalAvailableTickets' = totalAvailableTickets - 1

\* if user hits cancel, the temporary deposit goes to zero, all remaining coins back to user
Cancel == 
    /\ TransactionInProgress
    /\ insertedCoins' = 0
    /\ UNCHANGED << depositedCoins, totalAvailableTickets >>

\* all possible next behavior that the machine may have
Next == 
    \/ DeliverTicket
    \/ DepositCoin
    \/ Cancel


\* wf: fairness

Progress == WF_insertedCoins(Cancel)
    
Spec == Init /\ [][Next]_vars /\ Progress

====