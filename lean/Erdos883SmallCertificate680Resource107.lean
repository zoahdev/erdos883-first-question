import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_107 :
    (List.ofFn coreChunks680_107).flatten =
      (coreData680.take (coreResources680 107).q).drop 209 := by
  decide +kernel

theorem coreCheck680_107 :
    ∀ c : Fin 1, (coreChunks680_107 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 107)) = true := by
  decide +kernel
#print axioms coreFlatten680_107
#print axioms coreCheck680_107
end Erdos883Verified
