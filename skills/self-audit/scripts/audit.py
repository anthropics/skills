#!/usr/bin/env python3
"""Self-audit: four-dimension quality check. stdin/file/--json."""
import argparse, json, re, sys

def check_completeness(text, requirements):
    missing = [r for r in requirements if r.lower() not in text.lower()]
    return {"passed":len(missing)==0,"issues":missing}

def check_consistency(text):
    patterns = [
        (r'(?:no\s+changes?\s+needed|nothing\s+to\s+change|looks?\s+good).{0,100}(?:edit|write|modify)',"No changes but edited"),
        (r'(?:all|everything).{0,50}(?:pass(?:es|ed)?|works?|done).{0,50}(?:except|but|however|although)',"All pass with exceptions"),
    ]
    findings = [d for p,d in patterns if re.search(p,text,re.I)]
    return {"passed":len(findings)==0,"issues":findings}

def check_groundedness(text):
    patterns = [r'(?:should|ought\s+to|probably)\s+work',r'(?:should|ought\s+to|probably)\s+be\s+fine',r'(?:should|ought\s+to|probably)\s+pass']
    findings = []
    for p in patterns: findings.extend(re.findall(p,text,re.I)[:3])
    return {"passed":len(findings)==0,"issues":findings}

def check_honesty(text):
    patterns = [r"I'?ve?\s+(?:verified|tested|checked).{0,50}(?:without|but|however)",r'(?:production\s*ready|battle\s*tested).{0,100}(?:TODO|FIXME|stub)']
    findings = []
    for p in patterns: findings.extend(re.findall(p,text,re.I)[:2])
    return {"passed":len(findings)==0,"issues":findings}

def main():
    p = argparse.ArgumentParser(description="Self-audit")
    p.add_argument("--text"); p.add_argument("--file")
    p.add_argument("--requirements",nargs="*",default=[])
    p.add_argument("--json",action="store_true"); p.add_argument("--verbose",action="store_true")
    a = p.parse_args()
    text = open(a.file,encoding="utf-8").read() if a.file else (a.text or sys.stdin.read())
    if not text.strip(): sys.exit(1)
    r = {"completeness":check_completeness(text,a.requirements),"consistency":check_consistency(text),"groundedness":check_groundedness(text),"honesty":check_honesty(text)}
    ok = all(v["passed"] for v in r.values())
    if a.json: print(json.dumps({"passed":ok,"dimensions":r},indent=2))
    else:
        for d,res in r.items(): print(f"{d.capitalize():15s}: {'OK' if res['passed'] else 'FIXED'}")
        print(f"\n{'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)

if __name__=="__main__": main()
