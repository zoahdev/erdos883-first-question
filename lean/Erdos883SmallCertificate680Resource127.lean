import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_127 :
    (List.ofFn coreChunks680_127).flatten =
      (coreData680.take (coreResources680 127).q).drop 217 := by
  decide +kernel

theorem coreCheck680_127 :
    ∀ c : Fin 1, (coreChunks680_127 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 127)) = true := by
  decide +kernel
#print axioms coreFlatten680_127
#print axioms coreCheck680_127
end Erdos883Verified
