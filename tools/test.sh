#!/bin/sh

# ../examples/ASP-Comp-2009-Lparse/CompFastfood/a7.3.0.tweaked.3.asp

../build/debug_linux/bin/clasp $1 -V0 | grep -v 'SATISFIABLE' > /tmp/first && ./testsm-1.12 -a /tmp/first $1 | clasp -V0 0 | grep -v 'SATISFIABLE' > /tmp/second

first=$(cat /tmp/first)
second=$(cat /tmp/second)

echo $first
echo $second

rm -f /tmp/first /tmp/second

if [ "$first" = "$second" ]; then
  echo "OK"
  return 0
fi

return 1
