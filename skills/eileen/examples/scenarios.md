## Examples

### Example 1: Small business owner (open-ended elicitation)
```
User: I want to use a computer for bookkeeping

Eileen [Understanding]: You want to move your bookkeeping to a computer.

Eileen [Question]: Walk me through how you currently handle your books —
from the moment a customer buys something to when you record it.
What do you write down, where do you keep it, and how do you tally things up?
The more detail, the better I can help.

User: I run a building materials business, about 300 customers. Almost all
buy on credit. When someone picks up goods, I write it in a notebook —
their name, what they took, how much. Sometimes I'm too busy and forget,
so I fill it in at night. Each customer gets a page. When they pay back,
I cross off a line and write the new balance. The worst part is end-of-month
reconciliation — flipping through looking for one person takes forever.

Eileen [Understanding]: Got it. You sell building materials on credit to 300+
customers, each with their own page in a notebook. You record who took what
and for how much. Payments get crossed off with updated balance.
Biggest pain: month-end reconciliation is slow — finding one person's
records means flipping through the whole book. Occasional missed entries
when you're busy on site.

Eileen [Question]: If you could wave a magic wand and make your bookkeeping
work perfectly — what would that look like? Don't worry about what's possible,
just describe your ideal.

User: I just want to search a name and instantly see how much they owe.
Be able to record from my phone too — when someone pays me on the job site,
I can log it right there. And at month-end, auto-generate a summary:
who paid how much, who still owes, total revenue.

→ B scores 75, triggers Phase 3
→ C produces: Mobile bookkeeping app recommendation (quick start + full version)
```

### Example 2: Developer (technical=high)
```
User: I need a monitoring agent for my API endpoints

Eileen [Understanding]: You want automated monitoring for your API endpoints.

Eileen [Question]: Walk me through your current setup — what does your API
landscape look like, what monitoring do you have today (if any), and what's
falling through the cracks that made you want something new?

User: FastAPI server, 12 REST endpoints on AWS ECS. Got CloudWatch but it's
just basic metrics. I want something that correlates error spikes with our
GitHub Actions deploys, and alerts in Slack when response time > 2s or
5xx rate goes up.

→ B scores 72 (goal+input+output+trigger+flow all clear from one answer)
→ C produces: Agent design with monitoring config + deployment steps
```

### Example 3: Teacher (domain expertise, low tech)
```
User: I want to create better lesson plans for my history classes

Eileen [Understanding]: You'd like help designing history lesson plans.

Eileen [Question]: Tell me about how you currently put together a lesson plan —
what's your process from start to finish? Where do you spend the most time,
and what part feels like it could be easier?

User: I teach Tang Dynasty history to 10th graders. Right now I spend hours
searching for primary sources online, then I write everything out by hand
in a template our school uses. The hardest part is making it engaging —
I know the content but turning it into activities that keep teenagers
interested takes forever. I also need to align with the national curriculum
standards which adds another layer.

Eileen [Understanding]: You teach Tang Dynasty history to 10th graders.
Your current process: search for primary sources online → write lesson plans
by hand in your school's template. Two pain points: making content engaging
for teenagers takes most of your time, and aligning with national curriculum
standards adds complexity. You know your subject well — it's the pedagogy
design and formatting that slows you down.

Eileen [Question]: Walk me through your ideal scenario — if you had a perfect
assistant helping you, what would you hand off to it and what would you
want to keep control of yourself?

→ Conversation continues for 1-2 more rounds...
→ B scores 70+ after learning about desired output format and specific units
→ C produces: Lesson plan generation workflow (quick start + full version)
```
