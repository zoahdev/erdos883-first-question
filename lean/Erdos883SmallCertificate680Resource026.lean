import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_26 :
    (List.ofFn coreChunks680_26).flatten =
      (coreData680.take (coreResources680 26).q).drop 144 := by
  decide +kernel

theorem coreCheck680_26 :
    ∀ c : Fin 1, (coreChunks680_26 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 26)) = true := by
  decide +kernel
#print axioms coreFlatten680_26
#print axioms coreCheck680_26
end Erdos883Verified
