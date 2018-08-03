Require Import List Orders.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Sorticoq.SortedList.
Require Import Sorticoq.InsertionSort.
Import ListNotations.

Module BubbleSort (Import O: UsualOrderedTypeFull').

Include (OrderedTypeFacts O).

Definition A := O.t.




End BubbleSort.