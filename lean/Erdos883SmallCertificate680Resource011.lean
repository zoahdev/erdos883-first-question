import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_11 :
    (List.ofFn coreChunks680_11).flatten =
      (coreData680.take (coreResources680 11).q).drop 125 := by
  decide +kernel

theorem coreCheck680_11 :
    ∀ c : Fin 1, (coreChunks680_11 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 11)) = true := by
  decide +kernel
#print axioms coreFlatten680_11
#print axioms coreCheck680_11
end Erdos883Verified
