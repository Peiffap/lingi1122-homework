
datatype Tree = Vide
| Deux(Tree, int, Tree)
| Trois(Tree, int, Tree, int, Tree)

method insert2(t: Tree, i:int) returns (ret: Tree, isSame: bool)
    // Requires
    // Ensures
{
    match t
    case Vide => 
        ret := Deux(Vide, i, Vide); // empty
        isSame := false;
    case Deux(left, val, right) => // It was a 2-tree
        if (val > i)
        {
            var newLeft, cont := insert2(left, i);
            if(cont)
            {
                ret := Deux(newLeft, val, right);
                isSame := true;
            }
            else
            {
                match newLeft
                case Trois(leftC, valL, middleC, valR, rightC) =>
                    ret := Deux(newLeft, val, right);
                    isSame := false;
                case Vide => 
                    ret := Deux(newLeft, val, right);
                    isSame := true;
                case Deux(leftC, valC, rightC) =>
                    // Process to make a three of it
                    ret := Trois(leftC, valC, rightC, val, right);
                    isSame := true;
            }
        }
        else if(val < i)
        {
            var newRight, cont := insert2(right, i);
            if(cont)
            {
                ret := Deux(left, val, newRight);
                isSame := true;
            }
            else
            {
                match newRight
                case Trois(leftC, valL, middleC, valR, rightC) =>
                    ret := Deux(left, val, newRight);
                    isSame := false;
                case Vide =>
                    ret := Deux(left, val, newRight);
                    isSame := true;
                case Deux(leftC, valC, rightC) =>
                    ret := Trois(left, val, leftC, valC, rightC);
                    isSame := true;
            }
        }
        else
        {
            ret := t;
            isSame := true;
        }

    case Trois(left, valL, middle, valR, right) =>
        if (i < valL)
        {
            var newLeft, cont := insert2(left, i);
            if(cont)
            {
                ret := Trois(newLeft, valL, middle, valR, right);
                isSame := true;
            }
            else
            {
                match newLeft
                case Vide =>
                    ret := Trois(newLeft, valL, middle, valR, right);
                    isSame := true;
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(newLeft, valL, middle, valR, right);
                    isSame := true;
                case Deux(leftC, valC, rightC) =>
                    var rightBranch := Deux(middle, valR, right);
                    ret := Deux(newLeft, valL, rightBranch);
                    isSame := false;
            }
        }
        else if(i > valR)
        {
            var newRight, cont := insert2(right, i);
            if(cont)
            {
                ret := Trois(left, valL, middle, valR, newRight);
                isSame := true;
            }
            else
            {
                match newRight
                case Vide =>
                    ret := Trois(left, valL, middle, valR, newRight);
                    isSame := true;
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(left, valL, middle, valR, newRight);
                    isSame := true;
                case Deux(leftC, valC, rightC) =>
                    var leftBranch := Deux(left, valL, middle);
                    ret := Deux(leftBranch, valR, newRight);
                    isSame := false;
            }
        }
        else if(valL < i && i < valR)
        {
            var newMiddle, cont := insert2(middle, i);
            if(cont)
            {
                ret := Trois(left, valL, newMiddle, valR, right);
                isSame := true;
            }
            else
            {
                match newMiddle
                case Vide =>
                    ret := t; // Should be something different but I don't know
                    isSame := true;
                case Trois(leftC, valLC, middleC, valRC, rightC) =>
                    ret := Trois(left, valL, newMiddle, valR, right);
                    isSame := true;
                case Deux(leftC, valC, rightC) =>
                    var leftBranch := Deux(left, valL, leftC);
                    var rightBranch := Deux(rightC, valR, right);
                    ret := Deux(leftBranch, valC, rightBranch);
                    isSame := false;
            }
        }
        else{
            ret := t;
            isSame := true;
        }

}

method insert(t: Tree, i: int) returns (t': Tree)
    // Requires ...
    // Ensures ...
{
    var newNode, cont := insert2(t, i);
    t' := newNode;
}

method Main() {
var t := insert(Vide, 12); print t, "\n";
t := insert(t, 5); print t, "\n\n";
t := insert(t, 10); print t, "\n\n";
t := insert(t, 3); print t, "\n\n";
t := insert(t, 13); print t, "\n\n";
t := insert(t, 14); print t, "\n\n";
t := insert(t, 15); print t, "\n\n";
t := insert(t, 17); print t, "\n\n";
t := insert(t, 18); print t, "\n\n";
t := insert(t, 15); print t, "\n\n";
}