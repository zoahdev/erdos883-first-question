import Erdos883AdaptiveSpan104564Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength104564_8 : adaptiveNumericSpans104564_8.length = 642 := by decide +kernel
theorem adaptiveSpanEvenCache104564_8 : adaptiveSpanEven104564_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain104564_8 : adaptiveSpanEven104564_8.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanEvenEntries104564_8 : adaptiveSpanEven104564_8.spans = coreEvenSpans 52282 0 adaptiveNumericSpans104564_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache104564_8 : adaptiveSpanWhole104564_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain104564_8 : adaptiveSpanWhole104564_8.domainCheck 52282 = true := by decide +kernel
theorem adaptiveSpanWholeEntries104564_8 : adaptiveSpanWhole104564_8.spans = coreWholeSpans 0 adaptiveNumericSpans104564_8 := by
  decide +kernel
end Erdos883Verified
