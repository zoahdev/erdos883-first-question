import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_14 :
    (List.ofFn coreChunks680_14).flatten =
      (coreData680.take (coreResources680 14).q).drop 128 := by
  decide +kernel

theorem coreCheck680_14 :
    ∀ c : Fin 1, (coreChunks680_14 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 14)) = true := by
  decide +kernel
#print axioms coreFlatten680_14
#print axioms coreCheck680_14
end Erdos883Verified
