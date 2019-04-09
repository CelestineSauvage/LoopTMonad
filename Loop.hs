newtype LoopT c e m a r = LoopT
    { runLoopT ::     -- This universal quantification forces the
                                -- LoopT computation to call one of the
                                -- following continuations.
                  (c -> m r)    -- continue
               -> (e -> m r)    -- exit
               -> (a -> m r)    -- return a value
               -> m r
    }
