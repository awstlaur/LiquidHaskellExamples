{-@ reflect cycleTakeHelper @-}
cycleTakeHelper :: [a] -> [a] -> Int -> [a]
cycleTakeHelper _ _ 0         = []
cycleTakeHelper full [] n     = cycleTakeHelper full full n
cycleTakeHelper full (x:xs) n = x : (cycleTakeHelper full xs (n - 1))
