// Branch-and-bound tree for the branch-price-and-cut algorithm
#include "FTP.h"

struct Node nodeArray[MAXNODE];
struct Node head = Node();
struct Node s_head = Node();
struct Node stackBottom = Node();
struct Node listEnd = Node();
struct Node* listHead = &head;
struct Node* L_end = &listEnd;                   //linked list for the available nodes
struct Node* SlistHead = &s_head;                //Slist linked list
struct Node* bottom = &stackBottom;
struct Node* stackTop = bottom;              //stack, LIFO, at beginning the top pointer points to the bottom//

#pragma region "Available-Node-linked-list"
void listInit()//Initialize the linked list
{
    listHead->next = nodeArray;

    for (int i = 0; i < MAXNODE - 1; i++)
    {
        nodeArray[i] = Node();
        nodeArray[i].next = &nodeArray[i + 1];
    }
    nodeArray[MAXNODE - 1] = Node();
    nodeArray[MAXNODE - 1].next = NULL;
    L_end = &nodeArray[MAXNODE - 1];
    assert(L_end->next == NULL);
}

void listAdd(Node* n)  //add the free Node to the end of the available linked list
{
    *n = Node();//reinitialize the node
    L_end->next = n;
    L_end = L_end->next;
}

Node* listTake()//take the next available Node from the linked list
{
    Node* temp = NULL;
    if (listHead->next == NULL)//no one available, throw data structure exception
    {
        std::cerr << "\nERROR! Nodes in the available list out of use! \n";
        throw 'L';
    }
    else
    {
        temp = listHead->next;
        listHead->next = temp->next;
        temp->next = NULL;
        return temp;
    }
}
#pragma endregion

//for depth first search, also use the SlistNext pointers to manipulate the stack
#pragma region "Stack for DFS"
void stackInit()
{
    //point the top to the bottom, then the stack is empty
    while (stackTop != bottom) listAdd(stackPop());
}

int stackDepth()//give the depth of the stack
{
    int dep = 0;
    Node* current = stackTop;
    while (current != bottom)
    {
        current = current->SlistNext;
        dep++;
    }
    return dep;
}

void stackPush(Node* n)//push a Node into the stack
{
    n->SlistNext = stackTop;
    stackTop = n;
}

Node* stackPop()//pop the top element of the stack, NOTE: remember to recycle it
{
    if (stackTop != bottom)
    {
        Node* takenext = stackTop;
        stackTop = stackTop->SlistNext;
        takenext->SlistNext = NULL;
        return takenext;
    }
    else
    {
        std::cerr << "\n!!!Error! Failed to pop Node from the stack!\n";
        throw 'S';
    }
}

void stackPrune()
{
    //delete the top of stack until it can not be deleted
    while (globalUpperbound < stackTop->lowerbound + 1 + intTolerance && stackTop != bottom)
    {
        listAdd(stackPop());
    }
    if (stackTop != bottom)
    {
        //delete the nodes under the top
        Node* position = stackTop->SlistNext, * temp = stackTop;
        while (position != bottom)
        {
            if (globalUpperbound < 1 + position->lowerbound + intTolerance)
            {
                temp->SlistNext = position->SlistNext;
                listAdd(position);
                position = temp->SlistNext;
            }
            else
            {
                temp = temp->SlistNext;
                position = position->SlistNext;
            }
        }
    }
}
#pragma endregion