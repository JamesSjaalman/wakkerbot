Wakkerbot

The complete(?) history of wakkerbot, assembled from
a set of archived files I kept around on my filesystem.
All commits have been antedated using their filesystem dates.

Wakkerbot originates from Megahal, but has been seriously changed over time.

FYI: the original Megahal was licenced under a BSD-like licence (and is still available).
I narrowed the licence down to GPL3, which of course is only applicable to the changes I made.

		****************

Wakkerbot basically has two modes of action: training and generating.

	Training.
Training is done using flat text read from stdin. This input is tokenised, and the token -numbers are referred to in a Markov-"tree".
Whitespace is not considered part of a token, all other characters are.
Both tree-nodes and tokens carry statistics (counts), which are adjusted during training.

	Generating text.
Text generation uses stdin to read a (small) trigger corpus, from which a set of keywords is extracted.
From the Markov-trees a collection of sentences isgenerated. Each candidate sentence is scored using statistics from the trees and tokens, andweighted by the keyword-table.
The sentence with the highest score is kept and eventually output.

The "brain" is stored in a binary file, containing a small header, the forward and backward trees, and the token table. Both training and generating start by reading the brain from disk.
Training also rewrites the brain to disk.
A typical brain is ~3GB in size, and contains ~30M nodes and ~500K tokens.

During training, the brain grows. To keep the size needed within limits, occasionally the Alzheimer algorithm kicks in. The tree nodes carry timestamps, which are touched when the node is updated. Alzheimer decrements the refcounts for the oldest nodes and their referred symbols, and deletes them once the refcount reaches zero.
In the current version, tokens are never deleted. So, token numbers are stable, unreferenced tokens still exist and occupy space.
