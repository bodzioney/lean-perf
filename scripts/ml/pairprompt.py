"""The prompt of the step-contraction model: the same for training (build21.py) and for proposing
(scripts/pair-local)."""
import re

SYSTEM = ("You shorten Lean 4 tactic proofs. Given a theorem, the steps of its proof so far and some "
          "consecutive steps, answer with one tactic step that does the work of all of them. Answer with the step alone.")


def statement(text, limit=1200):
    """A declaration up to its proof, without its docstring, at most `limit` bytes from its end."""
    text = re.sub(r"^\s*/--.*?-/\s*", "", text, flags=re.S).strip()
    return text[-limit:]


def message(stmt, previous, steps, goal=""):
    """The user message. With the goal where the steps start (its last 1000 bytes: the target and
    the hypotheses nearest it), the statement is cut shorter."""
    prev = "\n".join(previous[-6:]) if previous else "(none)"
    run = "\n".join(steps)
    goal = goal.strip()
    if not goal:
        return f"Theorem:\n{statement(stmt)}\n\nSteps so far:\n{prev}\n\nReplace these steps with one:\n{run}"
    return (f"Theorem:\n{statement(stmt, 800)}\n\nSteps so far:\n{prev}\n\nGoal before these steps:\n"
            f"{goal[-1000:]}\n\nReplace these steps with one:\n{run}")


def glued(steps, answer):
    """Whether `answer` only joins the steps with `<;>` or `;`: as many parts as steps, each starting with
    its step's tactic name. Such an answer saves no work, so it is no contraction."""
    parts = [x.strip() for x in re.split(r"<;>|;", answer)]
    if len(parts) != len(steps):
        return False
    head = lambda t: re.match(r"[\w'?!.]*", t.strip()).group(0)
    return all(head(x) == head(y) for x, y in zip(parts, steps))
