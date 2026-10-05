import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_19 :
    (List.ofFn coreChunks680_19).flatten =
      (coreData680.take (coreResources680 19).q).drop 134 := by
  decide +kernel

theorem coreCheck680_19 :
    ∀ c : Fin 1, (coreChunks680_19 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 19)) = true := by
  decide +kernel
#print axioms coreFlatten680_19
#print axioms coreCheck680_19
end Erdos883Verified
