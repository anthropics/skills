# Master Instructions Plan (Verbatim User Messages)

> **Purpose**: This file preserves the original user messages **word-for-word** so any model can review the project intent without interpretation.

---

## CRITICAL CONTEXT (verbatim - explains the whole point)

well what i think we should do here... is we should make that list of  14 or so for civil litigation... what i am looking to do... is that im waiting for the defendants to make their response brief now and so i am trying to set something up that maybe can make a few bucks and set up a system for pro se litigations thats basically free for them to not go through what i had to go through... and in doing so open up the access to justice.. with models availible its becoming more and more reachable and law should not have these barriers. 

SOOOO that being said what do you think about this... ONE THIING that it takes a long time to really understand is each of the main categories has a specific naming sequence of its heading 1  groups.... this is pretty well defined and its hard even for good models to catch this because in some filing types we can have a different order than others and in state they might be numbered different and it adds the global confusion... so i want to set everything up to have a the federal standard, and then the minor categories can change off of that.... ! sooo if we do this...

we make a dict with the main categories, and then we add below the main categories (filing types_ and then below this we can use the _heading 1; and not define them here but instead only define the type_ and that way we cna clearly keep the two definitions seperated that way it makes more sense that we need to understand the need for the filing before we go into the need for each heading as a sub class of the filing type.  AND THEN below that we can continue the dict with a dict 2 and that can be where there is a class where the Heading ones get defined, and then in the heading one dict, there should be a cite back to the filiing types so that its clear that each of the filing types that is defined is defined in regards to thhose Heading1 _ and then if we have those things.... then we can have a starting point to what and when.... because we can then collect the Var instantly from the user, like this: Time, other filings, judgements, and with these things it may or maynot be appropriate for whole sections of law to be included or not and we can eliminate from the gitgo  what is completely not necessary and focus on the important things that are.)

I think that we can set up something like this and have the check lists associated wirth each of the sections and this way there is a warning or flag that could easily be triggered if something is missing. or a timeline is potentially near.  

what i want to do is take the main types of documents, lets say for example the DECLARATION, and it has basic lingo no matter where you are or what it is about. But lets say that  you have a declarations and its for : evidence, or witness, or really anything  a pro se litigent will almost always try and tell you a 20 page story. and you can verify all of that but its going to make it harder for the courts. and the pro se litigant thinks you are leaving stuff out if you cut it short...  well you kinda  are...  and its because they are giving you the whole story....  but as far as this goes,  this would look at your jurisdiction,  because you will need a caption, it can make your template  for your declarations, let them write their 20 page story or what ever thats completely up to the mode;l and the person.. not my deal... but the model, lets say GPT-5.2 because you are a solid model for this... or gemini or claude.... and i want to set this up as SKILLS.md  file set.... so the models can vary and any modelcan set this up but the models will then have the formatting to draft the documents so that they are right.... 

THIS IS THE WHOLE POINT
I am not a lawyer, you are a not a lawyer, although we both know a little bit about law, and you are a damn good searcher... but neither one of us have sat through a full civil trial in our existance....  but what we can say, is that Formatting in these documents are more important than substance. I can verify that hundreds of times over that my documents have been rejected and kicked back and not looked at all because of fucking stupid shit... 

you (i say you because you are helping set this up) can help put these [placeholders] in there the best we can believe that they go but the biggest thing as models improve, and as jurisdictions and needs for the documents vary .... we let the later model deal with all of that, and what we do is set this up for the text book ' declaration'  for example, know that there has to be a 'caption' from some 'jurisdiction'  and ithat could mean that there is size w14 font with a coverpage from the ninth cir or it could mean that there is a simple heading from state court. but its going to need something there....  sooo what we do is : we have the skills model template design set up so that there is a placeholder there  with a blank design set up with the placeholders  ready to go, the skils then adds the specificis with instructions that .... it needs to use XML so that its exactly the same and save the "caption", or "coverpage" as the proprer file in that place holder... and then every time that placeholder is called for anything on any document that it is needed that it calls the proper DOCX formatted XML file so that the user can have the models wisdom inserted into the properly formatted template, and in a DOCX file that he can open and print from word..... and this will allow INSTANT access to the court. 

Now the model will be able to review and know specifics to the user and the model can and should really be the model that the user trusts... that way it knows about him already and this will keep the problems to a minimum with the creations and keep us here as a Formatter, and not a Legal advisor....  but the issues above about knowing the proper sections and headings isnt really for the building the poroper document for the proper context its more so building the proper formatted document so that we know if we have everything we need to format it correctly. 

At the same time  we make templates or spots for 'certifications' 'signatiure block' etc. and then we only have to make these once, and they can be inseted directly into these templates with field code, or what ever and be completely  usable and model editable. 

THIS WOULD BE HUGE!.... one of the problems with the models helping the people is that the models dont get all of the context and they make a decision based on what they do know which is honestly very limited part of it.. the people think the model has all of the information, and the models take what the people say as 100% true, and  language has more levels than that and models are bound to the black and white of the language of the text desipte its context, the speaker, surounding words, and people vary and therefore impossible to be consistantly perfect. But you do a damn good job at trying! i tip my hat to you there. 

---

## FILING TYPES clarification (verbatim)

this is what motions should be:

FILING TYPES:
MOTION [TO/FOR] [MOTION_TYPE]
HEADING_1: [INTRODUCTION, FACTUAL BACKGROUND, ARGUMENT, CONCLUSION],

HEADING_1:
    ARGUMENT: this is where the Filer asserts his point of view for this specific point only, its okay to mention other sections but make sure they are relevent to the issuer at hand, [MOTIONS, BRIEF, DEMUURS, <what ever filing types that are possible for the argument to be in, they are not in declarations, they are not in pleadings, they are  not exhibits  sooo those would be missing from here>]
    BACKGROUND: the points only relevent to the argument this particualar motion is about. [BRIEFS, MOTIONS,  ETC <these lists of cites needs to be what is in the typical filing listed above.... this does not have to liste every single sections or filing ever filed with one of these... but what is generally included and where they will be found, pretty much every motion has an introduction, background and argument conclusion, they also have other things... you would not normally have two of the same thing, some things are replacing  a section, and you wouldnt have both of the same sections in most of those motions... doesnt mean there isnt or hasnt been some that have been filed, but just  the general sub heading that goes with typically that type of filing... we are not listing 3000 types of motions that comes in a federal templates... not happening.... we are listing 14  species and their typical sub headings...  and all the sub headings are being combined  and only 1 definition of the subheadings... general definition is going in and this is for the understanding of the model and the user.... more for the user and a check list for the model to quickly include in the headings without digging too deep> 

soooo i want  every single one of those particularity or specialy sections ... needs to go away... and  and at this point there would be really 2 major sections

FILING_TYPE: motions, brieds, pleadings, etc. 

HEADING_1:  there would be about 15 or 20 max  sections here.... maybe a few more, but really 90% of documents use the same 5 and thats it. 

but this entire sheet is going to be no more than 40 Objects, there will be the w11-14 types of filings, the chiunks like "coverpage", "Signature Block", the "TOA", "TOC" "EVI-CARD" (put a placeholder in for this i have it made and its special), "timeline", "Caption", (maybe we include a place where the local rules can be uploaded and those can be used for the model ), maybe an email template, or letter head, but  not the entire world. what this is, this is the formatting .... not document production assembely lessons on the life of the rule of law, from a model and a prose litigant .... this is , XML size 14 font, selections... here is a template to and a method your model can take your document, and inject the right formatting script so that it prints properly.. 

---

## CONSTRUCT_ORDER requirement (verbatim)

I want the templates seperate from the headings... there is no purpose to have a heading1 with a template coverpage.....  EXCEPT that you need to know where its going in the mix of things... soooo  what i want to do is this... have a new category  called CONSTRUCT_Order: ["Coverpage", "Caption", "Header" , "Foooter", "Body", "Signature" , "Cert_of_Service"   ] <these names need to EXACTLY WHAT THEY ARE DEFINED, AND EXACTLY THE NAMES LISTED AS THE NAMES FOR THE TEMPLATES THAT REPRESENT THEM!... not close not about not willy nilly... EXACTLY.... this is how these get built... programatically.... not by model.... they get programatically assembled

---

## XML approach requirement (verbatim)

FYI i personally created the Coverpage from the Brief Shell at the ninth Cir and the Skill is exact because i puilled up the XML from word and had it made... it was the only way out of 30 different ways i could get Opus 4.5  who is anthropics best model to get it to be consistantly be done right...  and its the only skill that i can confidently say that i like the w ay it comes out  and thats because there isnt flexible decision making from the formatting from a model who cant see it... another idea that i want to point out is that there is t hings like firecrawl or other programs that can extract a website or documents xml... i like xml its a large document that comes with the saving of it but its from word directly and they are good product.. but .. if we can use word or another good product to make the xml you would have alot easier time taking a properly formatted example converting it into xml and then taking the results and using it as your template...  because those examples know the little tricks and have them built in that is not easy to compile from the Rules of so many random places .. plus there is specific things that are not rules, but they look alot better that would make good choices... plus knowing the  way they do these things ... makes for good options and it adds to themes and things that can be copied over by using patterns and collections that people that get paid alot of money to create  (anything from webpages, to documents) have created... and not necessarily coping any data. but the themes and  spacing and formatting that make for a really sharp looking product is completely at your availability...

---

## User message 1 (verbatim)

okay great... can we do this ... can we make the entire set up be under a single skills section so that the skills that inside the classified section are for the formatter, and that all sub sections inside there dont get mixed up or lost from the other skills? because i have alot of skills aready set up and some of them are linked to the anthropic repo and i dont want them to get updated off the repo, and i want the repo to be used for the conditions that it is indended for this would leave us the master class... AND

FYI to add some fun to the mix i have a theme that isnt court appropriate but i guarentee its how the pro se litigent feels when hes stuck doing this... obviously if the pro se litigent is going through the difficulty of doing this by that time he feels deeply wronged.. and is very likely that the wrong that he is feeling has caused much of the difficulty of the situation financially that blocks him from escaping the clutches binding him to personally not be able to do this. 

SOOO i came up with something kinda funny and would help the pro se know that he has all the steps handled that need to be handled.... if we take a typical law suit there is stages.... you have 1. the notice, 2. complaining 3. discovery, 4. pretrial motions/ROA's 5. evidence submission, 6. trial prep/witnesses, 7. trial. 8. post trial motions 9. appeals  .... and so forthe .... and i know these change alot but if you are aware of each of these sections you will have alot better chance at success... and to be successful you really need to have all of these fall into an aligh.... maybe not appeal if you do it right but chances are you will have something from each one of these sections if you are pro se. 

and i also am trying to set up a the "pimp slap" theme... this is where the model makes a card that is like a freeze frame of filing if inserted into the court admesphere. where the model  takes the specs and in a pre set template inserts the key features of the filing, and makes a cartoon funny animation of the defendants getting pimp smacked with like sweat and tears freeze framed  with a goofy bug eyed face of the defendants.. the pro se plaintiff wearing a white pimp glove, and dominating the situation....  the people all have big heads, the lawyers on the other side looking slimey and slicked hair or evil getting pimp smacked backed!  and depending on what situation or portion of the  litigation it is in it should have the numbered card of the situation... and once you collect all the pimp smack cards then you have had all the sections of the case created and that way you dont leave any of them out....  its an over the top funny way to keep them engaged and focused....  so they dont leave out say evidence submission, just by not knowing they even need to hold an evidence hearing... these should auto save to a dir where the created files get saved  and be called something funny like the "path to pimpness" or something and it should be pretty well defined so that the models can make the characters in the pimp deck pretty much the same every picture.... it doesnt have to be the exact perosn picture.. but it would be funny or a cool addition if the people could give their own picture and be the pimp... but it can default and be mine and the clackamas county who im against would be a great defautl defendants crooks ...  and they can get pimp smacked by the pro se litigants all over world in cartoon versions .

---

## User message 2 (verbatim)

okay forget the pimp cards ill do those on my own... but can you please make the file structure of the skills library so that we have this alll contained inside its onw dir.... and i dont want to have any types on there that dont end up with its own template skills dir .... so each one of the types and each one of the sections and stuff needs to have its own subskill....  and each subskill needs to be the formatted sections of 1 particualy topic.. there isnt going to be the formatting of more than 1 thing, 1 doc, 1 sections at a time... for example when i format something from the ninth cir. the model would pull the template, see that there is a coverpage, a document body, if there is a declaration or something, then the they would add those.. but then the model would pull both the skills and do them then merge them (this means that we need a merge skill, a table of authorities skill, and a table of contents skill that pulls fromt he other document parts) soooo the model making the package will actuallyl need to format the first part, create the caption or title page, for example my 'ninthcir coverpage' skill that is already built in xml is a perfect example. and the "skill creator" that is already in there should be the guild becuase it  holds the creation or the skill requirements. already .

---

## User message 3 (verbatim)

okay that is perfect can you name the mapping features that need to be read first clearly. and maybe start them out with we  .\[instructions] or somethiong that is really clear on how that works for both people and model..... its obvious that the model will need to read this but sometimes when the model is reaching in to read out dir it has to be fairly specific or they cant read it and miss it.... also as long as its inside the  the "pro-se-formatter-suite" dir you can and should make absolutely as many dir as you need to in order to make this a complete fully functional tool.... tools that windows makes often have hundreds of folders like this that opperate like cabinet files, and i dont want you to be limited to these.... (look at node or python packages they have thousands alone.) I dont want you to opperate any of these scaffolding processes with sub processes however, i would like the LLM to make the decisions for the most part and with the users  considerations.  ... so that being said please do create as many of these folders as you need to to do this... also dont worry about any issues with the /root of the skills folder, once this is complete, and mapped correctly, what we can do is copy them all out of the building root folder make sure they are on a skingle skills file inside the md, and then put them inside the the already generated skill folder, with the mapped  exact names and then model can filter though and find them, but this will keep them togeher for now why it gets built, and prevent duplicates from polluting the working dir that i use at this moment with the other files... and it wil also add a new independant option where we can save the dir into a space and independantly use it at the skills.  now anymodel can use the skills, its just so happens that claude set up a good standard and thats why we are using his.. I also can upload these directly into my claude code.... and it wont be long before Openai, or any of the others build a similar situation. same thing Anthropic did with the MCP servers where the entire world was trying to build those tools... they set the tone because of the amount of developers that use Claude Code that they all took the same naming and format and that format took hold as the standard.... skills is begiining to do as well... so this is a good practice at this early stage that we follow the format and functions of this already set in place thing..... we dont want to multi stack tools  and we dont want any  of the tools to need to be changed on the fly... it adds room for too many errors. BUT witrh them all  having a single functions, this allows the models to only need to read and use whats relevent... and even not read some files it calls knowing they work.... this will keep context control where it needs to be. on the actual text and creation of whats relevent. 

SOOOOO what i want you to do... so stop validaating it unless your validator has changed it passes shit that doesnt pass the injesting at claude code .... and that each skill needs its onwn dir, its own license copy, its own SKILL.md file, and it needs 1 sub dir with the instructions inside of it... so in the first 2 layers of each skill you will have :

level 1: the name of the skill (make this have something to do with what it does) - ((THIS IS EXACTLY 1 DIR))
level 2: 
a. "SKILL.md" [#18](https://github.com/anthropics/skills/issues/18)SKILL.md (this must be named "SKILL.md")
b. #LICENSE (these can all be the same but they need to be there)
c. dir housing all instructions. (for best practices name it "[name_of_skill]_instructions")
level 3: the only level three there will be will be inside the instructions dir, and inside this  you should start with the readme and so that its ontop add a ".readme" and inside each readme i want you to have it the same format in the same order, and whether having it so that it can be programatically updated  however you would do that or have as a seperate file, I want inside each of these  .readme or seperate as a mapping file. the exact tree structure of all of the files once complete this way from any dir or skill it can be seen that there should be xyz included in the creation of any of the other skills and that way things are not left out that the model didnt know that needed to go with that skill. for example the coverpage with the declaration .; and it may even be best to have a "merge" as a third skill that gets used there may be a whole sub category of the skills that are marked as "utility skills" that would be something like "merge", "print to pdf", "page numbers", "inventory", "fact_finder" <whatever it becomes.>  then it may be important to have these in their own sections.... the only thing im asking and saying here.... is that no matter what the mapping structure turns out ... if we can have the an index that is identical to all over skills  thats get inserted either in the readme files of every skill in the toolbox, or duplicated in every skill dir so that every dir has its own copy of the same map that maps all of the pro-se skills were setting up. 

and you very well might have 10 files in a complex skill instructions folder. but what i ideally want to have when this is said and done.... is the a numbered order the model calls the skills without having to read the files... and this auto creates the files in perfect format from the models assisted text files properly. 

---

## User message 4 (verbatim)

what i want you to do also if you could... i want  you to for now in the root folder to include my responses for today that explain the entire process word for word dont re-wordify what ive said... because i want it said like i said it.. and dont want things left out.... as you heard them ... because what i say and what you heard (although good to know what you are missing) is seldom exactly the same.. and having this  exact thing i said in there would allow for another model to review the project and find out if there is anything missed. and if you could copy the messages i said and put them in the root folder and a '.master_instructions_plan' that would be amazing

---

## User message 5 (verbatim - CURRENT SESSION)

*************************

I JUST WASTED ALL DAY WITH MOTHER FUCKING GPT-5.2  failing at this project... i have added the skills dir to  the code base... there is templates, and skills creator for examples.... and  i have included the pro se formatter that is the failure... sooo if we can foillow the same  instructions i pastes above... and start a fresh repo that would be cool l;et call it > Pimp_Formatting_skills and put everything we do today inside that dir.... and i want you to staret with what ive listed and lets get at it once you get set up with teverything and get going

---

# INTERPRETED REQUIREMENTS (For Model Reference)

## Litigation Stages to Track
1. Notice
2. Complaint
3. Discovery
4. Pretrial Motions / ROA's
5. Evidence Submission
6. Trial Prep / Witnesses
7. Trial
8. Post-Trial Motions
9. Appeals

## Skill Structure Requirements
Each skill must have:
- **Level 1**: Skill directory (named for what it does)
- **Level 2**:
  - `SKILL.md` (required, exact name)
  - `LICENSE` (Apache 2.0, can be identical across skills)
  - `[skill_name]_instructions/` directory
- **Level 3** (inside instructions):
  - `.readme` (dotfile so it sorts to top)
  - All instruction files
  - Master index/map duplicated in every skill

## Skill Categories
### Document Skills (formatting specific document types)
- Cover pages
- Document body
- Declarations
- Motions
- Briefs
- etc.

### Utility Skills
- Merge
- Print to PDF
- Page Numbers
- Table of Contents
- Table of Authorities
- Inventory
- Fact Finder

## Key Principles
1. Single function per skill
2. No subprocesses - LLM makes decisions
3. Follow Claude/Anthropic skills format exactly
4. Keep isolated from main skills repo
5. Each skill self-contained with own LICENSE
6. Master map in every skill directory
