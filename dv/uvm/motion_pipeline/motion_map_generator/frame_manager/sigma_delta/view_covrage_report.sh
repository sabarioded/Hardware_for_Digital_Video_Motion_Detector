#!/usr/bin/env bash
make
urg -dir coverage.vdb
cd urgReport
firefox dashboard.html
