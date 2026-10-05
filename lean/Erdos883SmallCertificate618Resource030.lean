import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_30 :
    (List.ofFn coreChunks618_30).flatten =
      (coreData618.take (coreResources618 30).q).drop 143 := by
  decide +kernel

theorem coreCheck618_30 :
    ∀ c : Fin 1, (coreChunks618_30 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 30)) = true := by
  decide +kernel
#print axioms coreFlatten618_30
#print axioms coreCheck618_30
end Erdos883Verified
