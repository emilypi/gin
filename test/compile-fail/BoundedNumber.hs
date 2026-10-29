module BoundedNumber where

import Gin.Memory

invalid :: MemoryConfig
invalid = defaultMemoryConfig {memoryLanes = 0}
