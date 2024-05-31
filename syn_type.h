#pragma once

enum Status
{
    Swin,
    Ewin,
    Dfs_incomplete,
    Dfs_complete
};

enum Signal
{
    To_swin,
    To_ewin,
    Pending,
    Unsat
};