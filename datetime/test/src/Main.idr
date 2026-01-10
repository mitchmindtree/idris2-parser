module Main

import Hedgehog
import Props.DateTime

main : IO ()
main = test [ DateTime.props ]
