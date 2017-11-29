For [Alphabet](Alphabet.lagda.md) and [Generality](Generality.lagda.md):

-[ ] The research in these are interleaved with each other. I worry that the connections between these works will become frayed over time if not cut cleanly (separating concerns) or braided nicely (forming dependencies).

For [Alphabet](Alphabet.lagda.md):

-[ ] I would like to complete the the proof of isomorphism. Beyond that, `Alphabet` could be extended to demand that there is an encoding, similar to `language-to-alphabet`, of the terms to be modeled into the modeled `Alphabet.Term`, and that such a thing is an inverse of `Alphabet.reifyTerm`. (Because Agda does not, as of version 2.6.0-9496f75, allow `field` after `data` declarations within a `record`, such an extension would require a separate `record` type.)

-[ ] I worry that the `Alphabet` model would not fit a simply-typed lamda calculus (STLC). In Conor McBride's presentation of STLC, a term is indexed by the context of types in which it resides, `Cx ⋆`, and the type it inhabits, `⋆`. Thus an instance of my `Γ` would need to be something like `Cx ⋆ × ⋆`. His constructor of variable terms requires a type, such that my `V δ` would need to serve as context membership evidence of `δ` in `Γ`. I see now that I have, at best, a model of the untyped lamda calculus. I need to verify this, and in further research, I would like to create a model that covers both the untyped and simply-typed versions.

-[ ] The case for variables in the proof of `alphabet-to-alphabet` became far easier, as noted, after the change in parameterisation. I would like to study why this is, especially in connection with my other worries about ad-hoc-ness.

For [Generality](Generality.lagda.md):

-[ ] Say more precisely what it means "to find a language that `Stronger` can describe but `Collapsed` cannot". It may be helpful to consider what was discovered from `¬Γ⇒¬Weaker` and `¬[¬Γ⇒¬Stronger]`.

-[ ] Assuming that we indeed have, discover *why* we have gained by separating types `Γ` and `Δ`. Can we gain still further? Following an intuition I have, could it help to making one dependent on the other? Or to index each on a common type?

-[ ] Complete and clean-up the proof `Collapsed⇒Stronger.Alphabet`.

-[ ] Formalise a definition of a "1-1 mapping" with an eye towards defining what it means to be "more generally useful than".

-[ ] What then to say about the relation between "ad-hoc", "more generally useful than", and "1-1"? I seem to confirm fears about ad-hoc-ness of a given system by proving there is another system for which there is a 1-1 map "into it" from the alleged ad-hoc system. But how to put such fears to rest? Is there a certain respect in which I can say that a system is "most generally useful"?

For [BurnAfterReading](BurnAfterReading.lagda.md):

-[ ] Disperse parts to other files or trash.

For [Metaprogramming](Metaprogramming.lagda.md):

-[ ] Take code from [BurnAfterReading](BurnAfterReading.lagda.md).

For [Termination](Termination.lagda.md)

-[ ] Take code from [BurnAfterReading](BurnAfterReading.lagda.md).

For [Type](Type.lagda.md)

-[ ] Take code from [BurnAfterReading](BurnAfterReading.lagda.md).
