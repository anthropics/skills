# Detailed Criteria Reference

Full explanations, examples, and fix guidance for each of the 36 AI content quality criteria.

---

## Language and Tone Patterns

### 1. Undue Emphasis on Importance and Symbolism

**Pattern:** LLMs inflate the significance of subjects by connecting them to broader, often grandiose themes.

**Common phrases:**

- "stands as a testament to..."
- "plays a vital/significant/crucial role in..."
- "underscores its importance..."
- "leaves a lasting impact/legacy..."
- "serves as a reminder of..."
- "represents a milestone in..."
- "embodies the spirit of..."
- "symbolizes..."
- "carries enhanced significance..."

**Examples:**

- A local restaurant becomes "not just a place to eat, but a testament to community resilience"
- A minor product update "represents a watershed moment in technological innovation"
- A town is described as "a symbol of cultural heritage and economic vitality"

**Why this happens:** LLMs regress to the mean -- they emphasize what is statistically common (positive, grand descriptions) rather than what is actually notable or unique about the subject.

**The fix:** Ask: Is this subject genuinely significant in the way described? If not, describe it accurately rather than inflating its importance.

---

### 2. Promotional and Travel Brochure Language

**Pattern:** Content reads like marketing copy, especially for locations, cultural topics, or products.

**Common phrases:**

- "rich cultural heritage"
- "breathtaking"
- "stunning natural beauty"
- "must-visit destination"
- "captivating"
- "nestled in the heart of..."
- "boasts..."
- "offers a unique blend of..."
- "renowned for..."
- "fascinating"
- "diverse and vibrant"
- "hidden gem"

**Example passage:**

"Nestled in the heart of the countryside, the town of Millbrook boasts a rich cultural heritage and stunning natural beauty. This captivating destination offers visitors a unique blend of historic charm and modern amenities, making it a must-visit location for those seeking an authentic experience."

**The fix:** Replace promotional adjectives with specific, factual descriptions. What specifically makes it interesting? What would someone actually experience there?

---

### 3. Editorial Commentary and Meta-Analysis

**Pattern:** LLMs inject interpretation, importance judgments, or explicit guidance about what readers should think.

**Common phrases:**

- "it's important to note that..."
- "it is worth mentioning/noting..."
- "notably..."
- "significantly..."
- "interestingly..."
- "surprisingly..."
- "crucially..."
- "no discussion would be complete without..."
- "one cannot overlook..."
- "it should be emphasized that..."

**Why this violates journalistic standards:** Objective reporting presents facts and allows readers to form their own interpretations. These phrases signal editorializing.

**Example:**

"It's important to note that this development represents a significant shift in the industry, and it is worth emphasizing that stakeholders should pay close attention to these emerging trends."

**The fix:** State the facts. Trust readers to determine importance. If something is genuinely important, demonstrate it through evidence rather than declaring it.

---

### 4. Superficial Analysis with Participial Phrases

**Pattern:** Sentences end with "-ing" phrases that add shallow analytical commentary without substance.

**Structure:** [Statement], [participial phrase adding supposed insight]

**Examples:**

- "The company announced new policies, highlighting its commitment to sustainability."
- "The festival attracts thousands of visitors annually, underscoring the region's cultural importance."
- "The research revealed new findings, demonstrating the team's innovative approach."

**Why this is problematic:** The participial phrase adds apparent depth without providing actual analysis or evidence.

**The fix:** Either provide real analysis with evidence, or let the statement stand on its own.

---

### 5. Negative Parallelism

**Pattern:** LLMs overuse the "not X but Y" construction to create artificial contrast and drama.

**Common structures:**

- "It's not just X, but Y"
- "It's not only X, but also Y"
- "It is not merely X; it is Y"
- "X represents not only Y but also Z"

**Examples:**

- "The restaurant is not just a place to eat, but a cornerstone of community gathering."
- "This technology is not merely an improvement, but a revolutionary breakthrough."
- "The policy change represents not only a shift in strategy but also a commitment to transparency."

**The fix:** Use this structure sparingly and only when the contrast is genuine and significant.

---

### 6. Overuse of Transition Words and Formal Conjunctions

**Pattern:** Excessive, stilted use of transitional phrases that create an essay-like or overly formal tone.

**Common overused transitions:**

- "Moreover,"
- "Furthermore,"
- "Additionally,"
- "In addition,"
- "Nevertheless,"
- "On the other hand,"
- "Consequently,"
- "As a result,"

**Why this signals AI:** While professional writing uses transitions, LLMs overrely on a narrow set and place them mechanically rather than naturally.

**Human writing:** Uses varied transitions, including implicit transitions through logical flow, rather than explicit conjunctions at every paragraph break.

**The fix:** Let ideas connect through logical flow. When transitions are needed, vary them and use the simplest option that works.

---

### 7. Section-Ending Summaries

**Pattern:** Paragraphs or sections end with explicit summary statements, mimicking academic essay structure.

**Common phrases:**

- "In summary,"
- "In conclusion,"
- "Overall,"
- "To summarize,"
- "Ultimately,"
- "In essence,"

**Why this is problematic:** News articles, blogs, and most media content do not summarize sections like essays. Content flows naturally to the next point without explicit meta-commentary about summarizing.

**The fix:** Remove these phrases. If a section needs a summary to be understood, the section itself may need restructuring.

---

### 8. The Rule of Three

**Pattern:** Grouping ideas, traits, or examples in threes -- a legitimate rhetorical device that LLMs overuse formulaically.

**Common forms:**

- Three adjectives: "innovative, impactful, and transformative"
- Three short phrases: "boost morale, increase productivity, and foster collaboration"
- Three examples: "keynote sessions, panel discussions, and networking opportunities"
- Three qualities: "creative, smart, and funny"

**Why LLMs overuse this:** The rule of three is prevalent in training data (human writing, marketing, speeches), so LLMs default to it as a "safe" structure.

**Human writing:** Uses varied numbers of items naturally -- sometimes two, sometimes four, sometimes an uneven list. Does not mechanically group everything in threes.

**Detection tip:** Look for consistent triadic structure across multiple sentences and paragraphs.

**The fix:** Vary list lengths. Sometimes two items are enough. Sometimes four or five are warranted. Let content dictate structure, not formula.

---

### 9. Passive Voice and "Has Been Described As" Construction

**Pattern:** Overreliance on passive constructions and indirect attribution.

**Common phrases:**

- "[Subject] has been described as..."
- "[Subject] is widely regarded as..."
- "[Subject] is considered to be..."
- "[Subject] has been praised for..."
- "[Subject] is known for..."

**Why this signals AI:** LLMs use this construction to hedge when they lack specific knowledge or sources. It creates an illusion of authority without providing actual attribution.

**The fix:** Use direct statements with specific attribution: "According to [expert/organization], [subject]..."

---

### 10. Uniform Sentence and Paragraph Length

**Pattern:** Mechanically consistent structure -- every sentence approximately the same length, every paragraph the same size.

**Why this signals AI:** Human writing has natural rhythm and variation. Writers use short sentences for emphasis, long sentences for complex ideas, varied paragraph lengths for pacing.

**Detection tip:** Scan the visual structure of text. AI-generated content often looks like uniform blocks.

**The fix:** Vary sentence and paragraph length deliberately. Short sentences punch. Longer sentences can carry complexity when needed, building toward a point with subordinate clauses and careful construction. Some paragraphs should be brief. Others need room to develop.

---

## Style and Structural Indicators

### 11. Excessive Use of Em Dashes

**Pattern:** Overuse of em dashes where humans would use commas, parentheses, or colons.

**Why this signals AI:** LLMs were trained on professional writing where em dashes appear more frequently than in casual or journalistic writing. They default to em dashes for all parenthetical insertions.

**Note:** This indicator has limited shelf life as AI systems learn to avoid it. However, in combination with other patterns, it remains useful.

**Human pattern:** Uses varied punctuation (parentheses for asides, commas for clauses, colons for elaboration).

**The fix:** Use the punctuation mark that best fits the function. Em dashes for dramatic interruption or emphasis. Parentheses for true asides. Commas for standard clauses.

---

### 12. Bulleted Lists with Bolded Lead-ins

**Pattern:** Formulaic bullet points where each item begins with a bolded term followed by a colon and explanation.

**Structure:**

- **Scalability**: The system is designed to scale easily.
- **Flexibility**: Adapts to various use cases.
- **Efficiency**: Optimizes resource utilization.

**Why this signals AI:** This structure appears in AI-generated content far more than in human journalism or blog writing. Humans vary their list formats more naturally.

**Detection tip:** This pattern is especially strong when combined with generic bolded terms that simply restate what follows.

**The fix:** Vary list formats. Sometimes bullets without bold leads work better. Sometimes a numbered list fits. Sometimes prose serves better than a list at all.

---

### 13. Excessive Bolding and Formatting

**Pattern:** Mechanical, over-consistent use of bold text for key terms throughout an article.

**Why this signals AI:** LLMs sometimes emphasize terms they deem "important" without understanding that excessive formatting reduces readability.

**Human pattern:** Strategic use of formatting -- headlines, subheads, occasional emphasis, but not mechanical bolding of every "important" term.

**The fix:** Bold sparingly. If everything is emphasized, nothing is.

---

### 14. Emoji Usage in Inappropriate Contexts

**Pattern:** Emojis appearing in article text, headers, or formal content where they do not belong.

**Why this signals AI:** Some LLMs insert emojis to "add emotion" or "engage readers," but do so without understanding context or audience appropriateness.

**Note:** Emojis in social media posts, casual blogs, or intentionally informal content are normal. The tell is their appearance in contexts where they are inappropriate.

---

### 15. Markdown Formatting Mixed with Standard Text

**Pattern:** Presence of Markdown syntax elements in published content.

**Common artifacts:**

- Asterisks for bold/italic: `*emphasis*` or `**strong**`
- Underscores for emphasis: `_italic_`
- Hash symbols for headers: `## Section Title`
- Backticks for code: `` `inline code` ``
- Triple backticks for code blocks
- Numbers with periods for lists when not rendered: `1. First item`

**Why this happens:** LLMs are trained to output Markdown (used on GitHub, Reddit, Discord, etc.) and sometimes do not translate correctly to the target platform's formatting.

---

### 16. Curly vs. Straight Quotes

**Pattern:** Inconsistent use of curly quotes versus straight quotes or the wrong type for the context.

**Why this signals AI:** Different training data and platforms use different quote styles. LLMs may insert curly quotes in contexts where straight quotes are standard, or vice versa.

---

### 17. Title Case in Headers

**Pattern:** Section headers capitalize every major word (Title Case) instead of using sentence case.

**Examples:**

- AI: "The Evolution Of Modern Technology"
- Human journalism: "The evolution of modern technology"

**Why this signals AI:** Many LLMs default to title case for headers because it is common in certain types of content (marketing, academic), but most journalism uses sentence case.

---

## Technical and Formatting Tells

### 18. Placeholder Text and Incomplete Elements

**Pattern:** Bracketed placeholders left in published content.

**Common examples:**

- `[Insert source here]`
- `[Add specific example]`
- `[URL of reliable source]`
- `[Citation needed]`
- `[Date]`

**Why this happens:** A user copies AI-generated text with placeholders they were supposed to fill in but forgot.

**Variation:** Sometimes appears as XML-like notation: `:contentReference[oaicite:0]`

---

### 19. Chatbot Communication Artifacts

**Pattern:** Text that includes meta-communication between the chatbot and user.

**Examples:**

- Salutations: "Dear [Reader]," "Hello!"
- Valedictions: "Thank you for your time and consideration," "I hope this helps!"
- Instructions to user: "Here is your article on [topic]"
- Knowledge cutoff disclaimers: "As of my last training update in [date]..."
- Disclaimers: "Please consult a professional before..."
- Offers to assist further: "If you have any questions or need further clarification, feel free to ask!"

**Why this is a strong tell:** These phrases reveal that content was generated in response to a prompt and copied without editing.

---

### 20. Broken or Fabricated Links and Technical Codes

**Pattern:** Links, DOIs, ISBNs, or other technical identifiers that do not resolve or are invalid.

**Common issues:**

- URLs that lead to 404 errors
- DOIs that do not resolve to any article
- ISBNs with invalid checksums
- Generic placeholder links: `[Link to source]`
- ChatGPT-specific artifacts like "turn0search0"

**Why this happens:** LLMs hallucinate (fabricate) citations that look credible but do not actually exist.

**Detection method:** Click links, verify DOIs resolve, check ISBNs with checksum validators.

---

### 21. Citation Abnormalities

**Pattern:** References that appear legitimate but reveal AI generation upon inspection.

**Common issues:**

- Citations repeated multiple times without proper reference tagging
- Real sources cited for completely unrelated content
- Citations formatted in unusual or inconsistent styles
- Multiple citations to the same source without variation in attribution
- Generic citations: "According to experts..." without naming the experts

**Example of suspicious pattern:** Multiple identical citations in close proximity rather than using a single citation or cross-referencing.

---

### 22. Suspiciously Long or Elaborate Edit Summaries

**Pattern:** In platforms with edit tracking, unusually long, formal edit summaries written in first-person paragraphs.

**Example:**

"Refined the language of the article for a neutral, encyclopedic tone consistent with content guidelines. Removed promotional wording, ensured factual accuracy, and maintained a clear, well-structured presentation. Updated sections on history, coverage, challenges, and recognition for clarity and relevance."

**Why this signals AI:** Human editors typically write brief, informal edit summaries. LLMs generate formal, comprehensive summaries when prompted to explain changes.

---

## Citation and Sourcing Issues

### 23. Hallucinated Citations

**Characteristics:**

- Sources that sound credible but do not exist
- Misattribution of real sources to incorrect content
- Fabricated quotes from real people
- Non-existent journal articles with plausible-sounding titles
- Books or papers by real authors that do not exist

**Why this is critical:** Hallucinated citations are one of the most dangerous aspects of AI-generated content because they appear authoritative while spreading misinformation.

---

### 24. Vague Attribution to Unnamed Authorities

**Pattern:** Claims attributed to generic, unnamed sources.

**Examples:**

- "Experts say..."
- "Studies have shown..."
- "Research indicates..."
- "Analysts believe..."
- "Industry leaders suggest..."

**Without specific attribution:**

- Which experts?
- Which studies?
- What research?

**Professional standard:** Specific attribution with verifiable sources.

---

## Context-Specific Indicators

### 25. Industry-Specific Slop Patterns

Different domains show characteristic AI patterns:

**Technology writing:**

- Overuse of "innovative," "cutting-edge," "revolutionary"
- Generic descriptions: "robust," "scalable," "flexible"
- Buzzword clustering without substance

**Travel/lifestyle:**

- "Hidden gem," "off the beaten path"
- Excessive descriptors: "picturesque," "charming," "quaint"
- Generic itineraries: "must-see destinations"

**Business/corporate:**

- "Synergy," "leverage," "optimize"
- Mission statement language throughout
- "Game-changing," "paradigm shift"

**Product reviews:**

- Uniformly positive tone
- Generic praise without specific details
- Comparison charts without actual product experience

---

### 26. Lack of Personal Detail, Experience, or Specificity

**Pattern:** Generic descriptions without specific examples, personal anecdotes, or experiential details.

**AI writing:**

"The restaurant offers excellent service and a diverse menu featuring both traditional and innovative dishes."

**Human writing:**

"The waiter recommended the braised short rib after learning I don't eat seafood. The meat fell apart at the touch of my fork, and the red wine reduction had a subtle coffee undertone that lingered."

**Detection principle:** Humans who have experienced something provide specific sensory details, personal reactions, and concrete examples. AI generalizes.

---

### 27. Superficial Depth Without Expertise

**Pattern:** Content covers a topic broadly without demonstrating actual understanding or expertise.

**Characteristics:**

- Restates common knowledge without original insight
- Uses technical terms correctly but superficially
- Avoids controversial or nuanced aspects
- Provides "both sides" artificially balanced treatment
- Lacks specific examples, case studies, or detailed analysis

**Why this signals AI:** LLMs are trained on vast data but lack genuine expertise. They excel at sounding knowledgeable while avoiding depth that would reveal limitations.

**Sub-pattern — Balanced Hedging Conclusions:** A specific form of superficial depth where every section or the entire piece ends with equivocation rather than a position. "Ultimately, finding a balance between X and Y is crucial." "Both approaches have their merits and drawbacks." "The answer depends on your specific context." When a writer takes no stance on anything, they are summarizing a field, not working in it. Fix: take a position. State which approach is better and why. If both genuinely have merit in different contexts, name the contexts specifically instead of defaulting to "it depends."

---

## Hyperbolic and Dramatic Patterns

### 28. Hyperbolic Subheadings and Section Titles

**Pattern:** Subheadings that inflate the significance of the section's content rather than describing it.

**Examples:**

- "The word that changed everything"
- "A game-changing approach to X"
- "The revolutionary insight"
- "Why X will never be the same"
- "The surprising truth about X"
- "What nobody tells you about X"

**Why this signals AI:** LLMs optimize for engagement by default, producing subheadings that advertise rather than describe. Human writers working in editorial contexts use subheadings as navigation aids, not as marketing hooks for their own sections.

**The fix:** Subheadings should describe what the section contains. "The structural blind spot in test suites" tells you what you'll read. "The gap nobody talks about" tells you nothing except that the writer thinks they've discovered something important.

---

### 29. Dramatic Fragment Construction

**Pattern:** Short dramatic sentences or fragments used for artificial emphasis, creating theatrical pacing.

**Examples:**

- "And it was a disaster."
- "Everything changed."
- "The results were stunning."
- "But there was a problem."
- "That's when it clicked."

**Detection principle:** One or two dramatic fragments per article is a legitimate rhetorical device. A pattern of them — especially at section boundaries — is AI-style pacing that substitutes theatrics for substance. If every section opens with a short fragment or ends with a dramatic beat, the pacing is mechanical.

**The fix:** Let content create impact through specificity and evidence. "Revenue dropped 40% in six weeks" has more impact than "And then everything changed." Show, don't dramatize.

---

### 30. Borrowed Canonical Examples

**Pattern:** Using the same illustrative examples that appear in every article on a topic.

**Common borrowings:**

- "A jet engine is complicated; a market is complex" (Cynefin framework)
- "The bus route that nobody rides" (design thinking)
- "The restaurant with great food but no customers" (marketing/systems thinking)
- "The boiling frog" (change management)
- "The Swiss cheese model" (error prevention)

**Why this signals AI:** These examples are over-represented in training data because they appear in thousands of articles. A writer who uses them is summarizing a field. A writer who works in the field has their own examples drawn from their own experience.

**The fix:** Replace borrowed examples with original ones from your own work or construct novel ones that illustrate the same principle without recycling the same illustration everyone else uses.

---

## Confidentiality and Exposure Risks

### 31. Scenario Fingerprinting in "Anonymized" Examples

**Pattern:** Removing company names while keeping the scenario, specific numbers, stakeholder dynamics, vocabulary, and industry context. The scenario IS the identifier — names are the least important part.

**Example of false anonymization:** "A content platform used by journalists" where you "changed fourteen components from 'generate' to 'draft'" is identifiable to anyone who knows the author's work. The scenario, the exact number, the vocabulary change, and the industry context create a fingerprint that survives name removal.

**The four-test protocol before using any real example:**

1. **Outsider test:** Could a stranger narrow this to a small set of companies or situations?
2. **Insider test:** Does this confirm something an insider suspected but couldn't prove?
3. **Adversary test:** Could a reporter or competitor use this as evidence or ammunition?
4. **Irony test:** Does publishing this example undermine the very thing the example describes protecting?

If ANY test fails, the example cannot be used regardless of whether names are removed. Fix: transform the scenario, not just redact the names. Change the industry, the stakeholder type, the numbers, and the vocabulary simultaneously.

---

### 32. Operational Decisions Presented as Teaching Material

**Pattern:** Internal product strategy decisions, risk mitigation choices, and confidential operational changes described as case studies — even without names.

**Why this is dangerous:** If a decision was made to manage risk, describing it publicly re-creates the risk. An article about careful language choices that reveals you made those choices is self-defeating. A case study about restructuring a team to manage internal politics reveals the politics it was designed to manage.

**Fix:** Use genuinely universal patterns, publicly known examples from other companies (with attribution), fictional scenarios clearly marked as illustrative, or the author's personal methodology (which is already public). If the specifics of the decision are what makes the example valuable, the example is too specific to publish safely.

---

## Behavioral and Tonal Patterns

### 33. Saturated AI Vocabulary

**Pattern:** Clustering of words that appear at disproportionately high frequency in unedited AI output.

**The vocabulary list:**

delve, tapestry, nuanced, robust, foster, beacon, catalyst, synergy, pivotal, overarching, multifaceted, landscape (used abstractly), leverage (as verb), streamline, spearhead, underscore, harness, holistic, paradigm, empower, encompass, facilitate

**Detection principle:** Any single occurrence is unremarkable. These are legitimate English words that experts use naturally. The signal is clustering: three or more from this list in a single piece, or repeated use of the same word across sections, suggests unrevised AI output. "Nuanced" appearing once in a policy analysis is normal. "Nuanced" appearing four times alongside "robust," "pivotal," and "holistic" is a fingerprint.

**Why this signals AI:** LLMs over-index on words that are common in their training data's academic, corporate, and editorial registers. These words are individually correct but collectively distinctive because humans vary their vocabulary more.

**The fix:** Replace with concrete alternatives. "Delve into the nuances" becomes "examine the specifics." "A robust and holistic framework" becomes a description of what makes the framework strong and what it covers. "Foster synergy" becomes a description of what the collaboration actually produces.

---

### 34. Exhausted Metaphors as Structural Filler

**Pattern:** Dead metaphors used as connective tissue between ideas, simulating analytical sophistication without adding meaning.

**Common phrases:**

- "Navigating the complex landscape of..."
- "Viewed through the lens of..."
- "A symphony of moving parts"
- "At the intersection of X and Y"
- "The fabric of..." / "A tapestry of..."
- "Unpacking the layers of..."
- "In the ever-evolving world of..."
- "This opens the door to..."
- "Paving the way for..."

**Why these fail:** They function as transitions that connect ideas without saying anything about the connection. "Navigating the complex landscape of AI regulation" is a metaphor-shaped placeholder where an actual claim should be. Compare: "AI regulation is fragmented across jurisdictions, with no federal framework and conflicting state laws." The second says something. The first says nothing with more syllables.

**The fix:** State the actual relationship between ideas directly. If you find yourself reaching for a metaphor as a transition, ask: "What am I actually saying about how these ideas connect?" Write that instead.

---

### 35. Unprompted Moral Cadence

**Pattern:** Appending ethical reminders, aspirational statements, or "brighter future" codas to the end of factual, technical, or analytical content where the topic does not warrant moral framing.

**Examples:**

- A database optimization article ending with: "As we build these systems, we must remain mindful of their impact on society and work toward a more equitable technological future."
- A project management article concluding: "Ultimately, the true measure of success is not efficiency but the human connections we foster along the way."
- A code review guide finishing with: "By embracing these practices, we can create a more inclusive and compassionate engineering culture."

**Why this signals AI:** LLMs have a strong default toward positive, inclusive, aspirational conclusions regardless of topic. This is a training artifact — models are rewarded for producing content that feels uplifting and responsible. The result is a domain mismatch: the moral register of the conclusion does not match the analytical register of the preceding content.

**The fix:** End technical content with technical conclusions. If the topic genuinely raises ethical questions, address them with specificity and evidence, not platitudes. The test: does this moral conclusion follow from the preceding analysis, or was it appended because the model defaults to inspirational endings?

---

### 36. The Concierge Tone

**Pattern:** Pervasive sycophantic agreement, sterile professional empathy, and service-register language appearing in content that is not customer service.

**Manifestations:**

- **Excessive validation:** "That's a great question!" "What a wonderful observation!" "You're absolutely right to be concerned about this."
- **Hedged positivity:** Never saying something is wrong, bad, or a mistake. Everything is "an opportunity for improvement" or "an area for growth."
- **Formulaic empathy:** "I understand your concern." "That must be frustrating." "It's completely natural to feel that way."
- **Service-register framing:** Treating every reader interaction as a customer encounter. "I'd be happy to help with that." "Let me walk you through this."
- **Reflexive agreement:** Never disagreeing, never pushing back, never stating that an approach is wrong.

**Distinct from criterion 19 (Chatbot Artifacts):** Chatbot artifacts are structural tells — valedictions, help offers, knowledge disclaimers. The concierge tone is a tonal quality that pervades the entire piece. A writer can strip all chatbot artifacts and still write in concierge tone if the underlying register remains sycophantic.

**Why this signals AI:** Models are trained to be helpful and agreeable. In conversation, this is appropriate. In published content, it produces writing with no perspective, no critical judgment, and no willingness to tell the reader something they might not want to hear. Professional writing has a viewpoint. Service writing has a customer. Published content should not read like a customer service transcript.

**The fix:** Take positions. Disagree where warranted. State that something is wrong when it is wrong, not that it's "an area for potential improvement." Acknowledge limitations directly. The reader wants analysis, not accommodation.
