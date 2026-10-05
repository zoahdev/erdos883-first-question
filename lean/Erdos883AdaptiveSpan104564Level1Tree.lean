import Erdos883AdaptiveSpan104564Level1TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_1 : adaptiveNumericSpans104564_1.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_1 : adaptiveSpanEven104564_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_1 : adaptiveSpanEven104564_1.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_1 : adaptiveSpanEven104564_1.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_1 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_1 : adaptiveSpanWhole104564_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_1 : adaptiveSpanWhole104564_1.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_1 : adaptiveSpanWhole104564_1.spans = coreWholeSpans 0 adaptiveNumericSpans104564_1 := by
  decide +kernel
end Erdos883Verified
