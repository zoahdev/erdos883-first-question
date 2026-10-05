import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_117 :
    (List.ofFn coreChunks680_117).flatten =
      (coreData680.take (coreResources680 117).q).drop 276 := by
  decide +kernel

theorem coreCheck680_117 :
    ∀ c : Fin 1, (coreChunks680_117 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 117)) = true := by
  decide +kernel
#print axioms coreFlatten680_117
#print axioms coreCheck680_117
end Erdos883Verified
