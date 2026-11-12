#!/usr/bin/env python3
"""Close issues of this tracker that a merged nim-lang/nimony change fixes.

A fix names the issue in its PR body or commit message, e.g.

    Fixes planetis-m/nimony-bugs-fuzzers#12
    Closes https://github.com/planetis-m/nimony-bugs-llms/issues/40

Accepted verbs: fix, fixes, fixed, close, closes, closed, resolve, resolves,
resolved. A bare mention (no verb) only links; it never closes.

The script searches merged PRs and default-branch commits of the upstream repo
for this tracker's name, and closes every still-open issue they fix with a
comment that links the PR or commit. It is idempotent: closed issues are
skipped. Run with --dry-run to only print what it would do.

Env: GH_TOKEN (needs issues:write on this tracker), TRACKER (owner/name),
UPSTREAM (default nim-lang/nimony).
"""
import json, os, re, subprocess, sys

TRACKER = os.environ['TRACKER']
UPSTREAM = os.environ.get('UPSTREAM', 'nim-lang/nimony')
DRY = '--dry-run' in sys.argv
OWNER, NAME = TRACKER.split('/')
VERB = r'(?:fix(?:e[sd])?|close[sd]?|resolve[sd]?)'
REF = re.compile(
    VERB + r':?\s+(?:' + re.escape(TRACKER) + r'#|https://github\.com/'
    + re.escape(TRACKER) + r'/issues/)(\d+)\b', re.I)

def gh(*args):
    out = subprocess.run(['gh', 'api', *args], check=True, capture_output=True, text=True).stdout
    return json.loads(out) if out.strip() else None

def fixes(text):
    return {int(n) for n in REF.findall(text or '')}

def candidates():
    """(issue number, link text, link url) for every fix reference upstream."""
    q = f'repo:{UPSTREAM} is:pr is:merged "{TRACKER}"'
    for pr in gh('-X', 'GET', 'search/issues', '-f', f'q={q}', '-f', 'per_page=100')['items']:
        for n in fixes((pr.get('body') or '') + '\n' + pr['title']):
            yield n, f'{UPSTREAM}#{pr["number"]}', pr['html_url']
    q = f'repo:{UPSTREAM} "{TRACKER}"'
    res = gh('-X', 'GET', 'search/commits', '-f', f'q={q}', '-f', 'per_page=100',
             '-H', 'Accept: application/vnd.github+json')
    for c in res['items']:
        for n in fixes(c['commit']['message']):
            yield n, f'{UPSTREAM}@{c["sha"][:8]}', c['html_url']

def main():
    done = set()
    for n, label, url in candidates():
        if n in done:
            continue
        issue = gh(f'repos/{TRACKER}/issues/{n}')
        if issue is None or issue.get('state') != 'open':
            done.add(n); continue
        print(f'close #{n} <- {label}')
        if not DRY:
            gh('-X', 'POST', f'repos/{TRACKER}/issues/{n}/comments',
               '-f', f'body=Fixed upstream by {label} ({url}). Closed automatically by the close-fixed workflow.')
            gh('-X', 'PATCH', f'repos/{TRACKER}/issues/{n}', '-f', 'state=closed',
               '-f', 'state_reason=completed')
        done.add(n)
    print(f'{len(done)} referenced issue(s) checked')

if __name__ == '__main__':
    main()
