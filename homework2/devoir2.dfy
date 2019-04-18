
datatype Tree = Vide
| Deux(Tree, int, Tree)
| Trois(Tree, int, Tree, int, Tree)

method insert2(t: Tree, i:int) returns (ret: Tree, contains: bool)
    // Requires
    // Ensures
{
    match t
    case Vide => ret := Deux(Vide, i, Vide); // empty
    case Deux(left, val, right) => // It was a 2-tree
        if (val > i)
        {
            var newLeft, cont := insert2(left, i);
            if(cont)
            {
                ret := t;
                contains := true;
            }
            else
            {
                match newLeft
                case Trois(leftC, valL, middleC, valR, rightC) =>
                    ret := Deux(newLeft, val, right);
                case Vide => 
                    ret := Deux(newLeft, val, right);
                case Deux(leftC, valC, rightC) =>
                    // Process to make a three of it
                    ret := Trois(leftC, valC, rightC, val, right);
            }
        }
        else if(val < i)
        {
            var newRight, cont := insert2(right, i);
            if(cont)
            {
                ret := t;
                contains := true;
            }
            else
            {
                match newRight
                case Trois(leftC, valL, middleC, valR, rightC) =>
                    ret := Deux(left, val, newRight);
                case Vide =>
                    ret := Deux(left, val, newRight);
                case Deux(leftC, valC, rightC) =>
                    ret := Trois(left, val, leftC, valC, rightC);
            }
        }
        else
        {
            ret := t;
        }

    case Trois(left, valL, middle, valR, right) =>
        if (i < valL)
        {
            var newLeft, cont := insert2(left, i);
            if(cont)
            {
                ret := t;
                contains := true;
            }
            else
            {
                match newLeft
                case Vide =>
                    ret := Trois(newLeft, valL, middle, valR, right);
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(newLeft, valL, middle, valR, right);
                case Deux(leftC, valC, rightC) =>
                    var rightBranch := Deux(middle, valR, right);
                    ret := Deux(newLeft, valL, rightBranch);
            }
        }
        else if(i > valR)
        {
            var newRight, cont := insert2(right, i);
            if(cont)
            {
                ret := t;
                contains := true;
            }
            else
            {
                match newRight
                case Vide =>
                    ret := Trois(left, valL, middle, valR, newRight);
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(left, valL, middle, valR, newRight);
                case Deux(leftC, valC, rightC) =>
                    var leftBranch := Deux(left, valL, middle);
                    ret := Deux(leftBranch, valR, newRight);
            }
        }
        else if(valL < i && i < valR)
        {
            var newMiddle, cont := insert2(middle, i);
            if(cont)
            {
                ret := t;
                contains := true;
            }
            else
            {
                match newMiddle
                case Vide =>
                    ret := t; // Should be something different but I don't know
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(left, valL, newMiddle, valR, right);
                case Deux(leftC, valC, rightC) =>
                    var leftBranch := Deux(left, valL, leftC);
                    var rightBranch := Deux(rightC, valR, right);
                    ret := Deux(leftBranch, valC, rightBranch);
            }
        }
        else{
            ret := t;
        }

}

method insert(t: Tree, i: int) returns (t': Tree)
    // Requires ...
    // Ensures ...
{
    var newNode := insert2(t, i);
    t' := newNode;
}

method Main() {
var t := insert(Vide, 1); print t, "\n";
t := insert(t, 2); print t, "\n";
t := insert(t, -1); print t, "\n";
t := insert(t, 0); print t, "\n";
t := insert(t, -2); print t, "\n";
}