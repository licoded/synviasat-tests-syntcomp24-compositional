#ifndef __MY_CUSTOM_GRAPH__
#define __MY_CUSTOM_GRAPH__

#include <iostream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
using namespace std;

template<typename T, typename K>
struct MyEdge
{
    T label;
    K dest;
};

template<typename NodeIdType, typename LabelType>
class MyGraph
{
public:
    unordered_set<NodeIdType> vertices;
    using EdgeType = MyEdge<LabelType, NodeIdType>;
    unordered_map<NodeIdType, vector<EdgeType>> edges;

    void add_vertex(NodeIdType v)
    {
        if (vertices.find(v) == vertices.end())
        {
            vertices.insert(v);
        }
    }

    void add_edge(NodeIdType src, NodeIdType dest, LabelType label)
    {
        add_vertex(src);
        add_vertex(dest);
        // NOTE: we don't check if the edge already exists here, 
        //       no-repeatition should be ensured by users
        edges[src].push_back({label, dest});
    }
};


#endif