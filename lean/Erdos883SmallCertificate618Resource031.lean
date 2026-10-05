import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_31 :
    (List.ofFn coreChunks618_31).flatten =
      (coreData618.take (coreResources618 31).q).drop 144 := by
  decide +kernel

theorem coreCheck618_31 :
    ∀ c : Fin 1, (coreChunks618_31 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 31)) = true := by
  decide +kernel
#print axioms coreFlatten618_31
#print axioms coreCheck618_31
end Erdos883Verified
