import Erdos883AdaptiveSpan104564Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_2 : adaptiveNumericSpans104564_2.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_2 : adaptiveSpanEven104564_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_2 : adaptiveSpanEven104564_2.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_2 : adaptiveSpanEven104564_2.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_2 : adaptiveSpanWhole104564_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_2 : adaptiveSpanWhole104564_2.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_2 : adaptiveSpanWhole104564_2.spans = coreWholeSpans 0 adaptiveNumericSpans104564_2 := by
  decide +kernel
end Erdos883Verified
