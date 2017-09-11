unification rant on the royal road to Agda (feat. Emmylou Harris with Ricky Skaggs)

* What is the minimum standard that unification must meet?

* Please forgive the following rant.

It's infuriating to me that I have such a hard time predicting whether a given program will type-check. I'm starting to think that dependent-type programming is unavoidably hard because of undecidability: any such language will employ some arbitrary unification algorithm which fails to solve certain cases; but unless the programmer knows that algorithm, he won't be able to always predict what code will and won't be accepted by the type-checker. And even if he does (and I don't), it wouldn't be much help, practically speaking. Therefore, programmers in dependent types are best-off learning heuristics to get them around the language, sometimes through trial-and-error, rather than through a bottom-up understanding.

* As a programmer in Agda, would I be well-advised to learn the details of the unification machinery? Or better to just continue "learning by doing"?

I imagine a saving-grace would be if the language allowed for custom meta-solvers (mentioned in Agda issue #2513), so that programmers could fill-in the gaps that they otherwise would have expected the type-checker to handle. But maybe I'm mistaking a rabbit-hole for a green pasture.

* How's my imagination? And how long-off till we reach that "heavenly shore"?
