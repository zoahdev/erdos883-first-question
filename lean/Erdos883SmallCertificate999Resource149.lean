import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_149 :
    (List.ofFn coreChunks999_149).flatten =
      (coreData999.take (coreResources999 149).q).drop 257 := by
  decide +kernel

theorem coreCheck999_149 :
    ∀ c : Fin 1, (coreChunks999_149 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 149)) = true := by
  decide +kernel
#print axioms coreFlatten999_149
#print axioms coreCheck999_149
end Erdos883Verified
