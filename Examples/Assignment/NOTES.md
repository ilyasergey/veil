# Design notes

One page at most. Short answers in your own words are enough.

## Time and tools

- Time spent, roughly, on: setup and reading / the model / properties and checks.
- AI agents or other tools used, and for what.
- What is unfinished, if anything.

## The model

- What the state consists of, and why each part is there.
- The actions, and which component (sender, receiver, link, client) takes each.
- What the links can do to frames, and what they cannot.
- Every bound in the model, and what it rules out.
- Where the model deviates from the sources you used.

## Safety

- Each `safety` clause in one sentence of plain English.
- A fault each clause would catch.
- A fault that none of them would catch, if you can think of one.

## Reachability

- The witnesses you asked for, and what each one shows.
- The instance and bounds they were found on.

## Liveness

- The property in one sentence of plain English.
- The fairness assumptions under which it holds, and what each means in a real system.
- The weaker assumptions under which it fails, and the run that the checker reports.

## Limits

- What your checks establish, and for which instances.
- What you would do next with another day.
