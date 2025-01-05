# Uniform Word Problem for Ortholattices Solver

## Overview

This project aims to solve the **Uniform Word Problem for Ortholattices** using a backward algorithm within the **LISA** environment. The Uniform Word Problem (UWP) for groups and lattices is a decision problem where we aim to determine if two terms are equal under a given set of axioms or relations. In the case of ortholattices, which are partially ordered structures with properties similar to Boolean algebras, the problem is tackled using a backward search approach, leveraging the unique properties of ortholattices.

## Problem Description

The **Uniform Word Problem** for a group or lattice involves finding an algorithm to determine if two terms in the group or lattice are equal. In this project, we focus on ortholattices and a finite presentation based on **inequalities** (e.g., `<=`, `>=`). The key idea is to use backward reasoning to derive a solution to the word problem under a set of given axioms. The goal is to check if two terms, represented in the formalism of ortholattices, are equivalent by deriving a proof using backward reasoning.

## Features

- **Backward Algorithm**: The algorithm employs a backward search strategy to solve the Uniform Word Problem. It starts from the goal and recursively tries to apply available tactics to reach the conclusion.
- **Ortholattice Formalism**: The project is focused on **ortholattices**, which are algebraic structures equipped with operations like meet (`∧`), join (`∨`), and negation (`¬`). The focus is on **inequality** relations (`<=`, `>=`).
- **Implementation in LISA**: The algorithm is implemented in the LISA environment.



