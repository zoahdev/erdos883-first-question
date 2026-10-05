import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_148 :
    (List.ofFn coreChunks999_148).flatten =
      (coreData999.take (coreResources999 148).q).drop 256 := by
  decide +kernel

theorem coreCheck999_148 :
    ∀ c : Fin 1, (coreChunks999_148 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 148)) = true := by
  decide +kernel
#print axioms coreFlatten999_148
#print axioms coreCheck999_148
end Erdos883Verified
