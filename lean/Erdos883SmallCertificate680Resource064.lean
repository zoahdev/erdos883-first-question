import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_64 :
    (List.ofFn coreChunks680_64).flatten =
      (coreData680.take (coreResources680 64).q).drop 124 := by
  decide +kernel

theorem coreCheck680_64 :
    ∀ c : Fin 1, (coreChunks680_64 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 64)) = true := by
  decide +kernel
#print axioms coreFlatten680_64
#print axioms coreCheck680_64
end Erdos883Verified
